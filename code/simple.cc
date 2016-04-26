/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "simple.hh"

#include <set>
#include <map>
#include <vector>
#include <algorithm>

#include <iostream>

using std::map;
using std::set;
using std::vector;
using std::pair;
using std::greater;

using std::cout;
using std::cerr;
using std::endl;

namespace
{
    struct Variables
    {
        Variables(unsigned)
        {
        }

        map<unsigned, set<unsigned> > domains;
        pair<unsigned, unsigned> assignment;
    };

    struct VariablesStack
    {
        vector<Variables> variables;

        VariablesStack(unsigned depth, unsigned width) :
            variables(depth + 1, Variables{ width })
            {
            }
    };

    using FalseImplication = vector<pair<unsigned, unsigned> >;

    using LearnedNogoods = set<FalseImplication>;

    auto initialise_variables(const pair<Graph, Graph> & graphs, const Params &, Variables & variables)
    {
        vector<unsigned> pattern_degrees(graphs.first.size()), target_degrees(graphs.second.size());
        vector<vector<unsigned> > pattern_nds(graphs.first.size()), target_nds(graphs.second.size());

        for (unsigned p = 0 ; p < graphs.first.size() ; ++p)
            pattern_degrees[p] = graphs.first.degree(p);

        for (unsigned p = 0 ; p < graphs.first.size() ; ++p) {
            for (unsigned q = 0 ; q < graphs.first.size() ; ++q)
                if (graphs.first.adjacent(p, q))
                    pattern_nds[p].push_back(pattern_degrees[q]);
            sort(pattern_nds[p].begin(), pattern_nds[p].end(), greater<unsigned>());
        }

        for (unsigned t = 0 ; t < graphs.second.size() ; ++t)
            target_degrees[t] = graphs.second.degree(t);

        for (unsigned t = 0 ; t < graphs.second.size() ; ++t) {
            for (unsigned u = 0 ; u < graphs.second.size() ; ++u)
                if (graphs.second.adjacent(t, u))
                    target_nds[t].push_back(target_degrees[u]);
            sort(target_nds[t].begin(), target_nds[t].end(), greater<unsigned>());
        }

        for (unsigned p = 0 ; p < graphs.first.size() ; ++p) {
            variables.domains.emplace(p, set<unsigned>());
            for (unsigned t = 0 ; t < graphs.second.size() ; ++t) {
                if (graphs.first.adjacent(p, p) == graphs.second.adjacent(t, t))
                    if (pattern_degrees[p] <= target_degrees[t]) {
                        bool ok = true;
                        for (unsigned x = 0 ; x < pattern_degrees[p] ; ++x)
                            if (pattern_nds[p][x] > target_nds[t][x]) {
                                ok = false;
                                break;
                            }

                        if (ok)
                            variables.domains[p].insert(t);
                    }
            }
        }
    }

    auto smallest_domain(Variables & variables) -> map<unsigned, set<unsigned> >::iterator
    {
        return min_element(variables.domains.begin(), variables.domains.end(),
                [] (const auto & a, const auto & b) {
                    return a.second.size() < b.second.size();
                    });
    }

    auto learn_greedy(const pair<Graph, Graph> & graphs,
            const VariablesStack & variables_stack, unsigned stack_level, LearnedNogoods & learned_nogoods,
            const unsigned failed_variable)
    {
        FalseImplication new_nogood;

        auto unseen = variables_stack.variables.at(0).domains.find(failed_variable)->second;

        // remove any 1 nogoods
        for (auto & n : learned_nogoods)
            if (n.size() == 1 && n[0].first == failed_variable)
                unseen.erase(n[0].second);

        vector<pair<unsigned, set<unsigned> > > disallowed_by_level(stack_level + 1);

        for (unsigned d = stack_level ; d >= 1 ; --d) {
            const auto & d_variables = variables_stack.variables.at(d);

            disallowed_by_level.at(d).first = d;
            disallowed_by_level.at(d).second.emplace(d_variables.assignment.second);
            if (graphs.first.adjacent(d_variables.assignment.first, failed_variable))
                for (unsigned t = 0 ; t < graphs.second.size() ; ++t)
                    if (! graphs.second.adjacent(d_variables.assignment.second, t))
                        disallowed_by_level.at(d).second.emplace(t);
        }

        while (! unseen.empty()) {
            auto & d = *max_element(disallowed_by_level.rbegin(), disallowed_by_level.rend(),
                    [] (const auto & a, const auto & b) {
                        return a.second.size() < b.second.size();
                    });

            if (d.second.empty()) {
                return;
            }

            bool reduced = false;
            for (auto & v : d.second)
                if (unseen.count(v)) {
                    reduced = true;
                    unseen.erase(v);
                }

            if (reduced) {
                new_nogood.emplace_back(variables_stack.variables.at(d.first).assignment);

                // now look for unit propagation based upon the current nogood
                for (auto & nogood : learned_nogoods) {
                    bool contradicted = false;
                    unsigned matches = 0, mismatches = 0;
                    pair<unsigned, unsigned> missed_clause;

                    for (auto & a : nogood) {
                        unsigned found = false;
                        for (auto & n : new_nogood) {
                            if (n == a) {
                                found = true;
                                break;
                            }
                            else if (n.first == a.first) {
                                contradicted = true;
                                break;
                            }
                        }

                        if (found)
                            ++matches;
                        else
                            missed_clause = a;

                        if (mismatches > 1)
                            break;
                    }

                    if ((! contradicted) && (matches == nogood.size() - 1) && missed_clause.first == failed_variable) {
                        auto to_remove = missed_clause.second;
                        unseen.erase(to_remove);
                        for (auto & l : disallowed_by_level)
                            l.second.erase(to_remove);
                    }
                }
            }

            auto to_remove = d.second;
            for (auto & l : disallowed_by_level) {
                for (auto & r : to_remove)
                    l.second.erase(r);
            }
        }

        learned_nogoods.insert(new_nogood);
    }

    auto solve(const pair<Graph, Graph> & graphs, const Params & params, Result & result,
            VariablesStack & variables_stack, unsigned stack_level,
            LearnedNogoods & learned_nogoods) -> bool
    {
        if (*params.abort)
            return false;

        ++result.nodes;

        auto & variables = variables_stack.variables.at(stack_level);

        auto branch_variable = smallest_domain(variables);
        if (branch_variable == variables.domains.end())
            return true;

        if (branch_variable->second.empty()) {
            learn_greedy(graphs, variables_stack, stack_level, learned_nogoods, branch_variable->first);

            return false;
        }

        vector<unsigned> branch_values(branch_variable->second.begin(), branch_variable->second.end());
        sort(branch_values.begin(), branch_values.end(), [&] (auto & a, auto & b) {
                return graphs.second.degree(a) > graphs.second.degree(b);
                });

        for (const auto & t : branch_values) {
            result.isomorphism[branch_variable->first] = t;

            auto & next_variables = variables_stack.variables.at(stack_level + 1);
            next_variables = variables;

            next_variables.domains.erase(branch_variable->first);
            next_variables.assignment = { branch_variable->first, t };

            for (auto & d : next_variables.domains) {
                // propagate all-different
                d.second.erase(t);

                // propagate adjacency
                if (graphs.first.adjacent(branch_variable->first, d.first)) {
                    for (auto i = d.second.begin() ; i != d.second.end() ; ) {
                        if (graphs.second.adjacent(t, *i))
                            ++i;
                        else
                            d.second.erase(i++);
                    }
                }
            }

            // propagate learning
            bool state_is_nogood = false;
            for (auto & nogood : learned_nogoods) {
                bool contradicted = false;
                unsigned matches = 0, mismatches = 0;
                pair<unsigned, unsigned> missed_clause;

                for (auto & a : nogood) {
                    unsigned found = false;
                    for (unsigned d = 1 ; d <= stack_level + 1 ; ++d) {
                        if (variables_stack.variables.at(d).assignment == a) {
                            found = true;
                            break;
                        }
                        else if (variables_stack.variables.at(d).assignment.first == a.first) {
                            contradicted = true;
                            break;
                        }
                    }

                    if (found)
                        ++matches;
                    else
                        missed_clause = a;

                    if (mismatches > 1)
                        break;
                }

                if (! contradicted) {
                    if (matches == nogood.size()) {
                        state_is_nogood = true;
                    }
                    else if (matches == nogood.size() - 1) {
                        auto v = next_variables.domains.find(missed_clause.first);
                        if (v == next_variables.domains.end()) throw 0;
                        v->second.erase(missed_clause.second);
                    }
                }
            }

            if ((! state_is_nogood) && solve(graphs, params, result, variables_stack, stack_level + 1, learned_nogoods))
                return true;
        }

        return false;
    }
}

auto simple_subgraph_isomorphism(const pair<Graph, Graph> & graphs, const Params & params) -> Result
{
    Result result;

    VariablesStack variables_stack(graphs.first.size(), graphs.second.size());
    LearnedNogoods learned_nogoods;

    initialise_variables(graphs, params, variables_stack.variables.at(0));
    if (! solve(graphs, params, result, variables_stack, 0, learned_nogoods))
        result.isomorphism.clear();

    map<unsigned, unsigned> clauses;
    for (auto & n : learned_nogoods)
        clauses[n.size()]++;

    cout << "Learned " << learned_nogoods.size() << ":";
    for (auto & c : clauses)
        cout << " " << c.first << "=" << c.second;
    cout << endl;

    return result;
}

