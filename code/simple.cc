/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "simple.hh"

#include <set>
#include <map>
#include <algorithm>

#include <iostream>

namespace
{
    struct Variables
    {
        Variables(unsigned)
        {
        }

        std::map<unsigned, std::set<unsigned> > domains;
        std::pair<unsigned, unsigned> assignment;
    };

    struct VariablesStack
    {
        std::vector<Variables> variables;

        VariablesStack(unsigned depth, unsigned width) :
            variables(depth + 1, Variables{ width })
            {
            }
    };

    using FalseImplication = std::vector<std::pair<unsigned, unsigned> >;

    using LearnedNogoods = std::set<FalseImplication>;

    auto initialise_variables(const std::pair<Graph, Graph> & graphs, const Params &, Variables & variables)
    {
        for (unsigned p = 0 ; p < graphs.first.size() ; ++p) {
            variables.domains.emplace(p, std::set<unsigned>());
            for (unsigned t = 0 ; t < graphs.second.size() ; ++t) {
                if (graphs.first.adjacent(p, p) == graphs.second.adjacent(t, t))
                    if (graphs.first.degree(p) <= graphs.second.degree(t))
                        variables.domains[p].insert(t);
            }
        }
    }

    auto smallest_domain(Variables & variables) -> std::map<unsigned, std::set<unsigned> >::iterator
    {
        return std::min_element(variables.domains.begin(), variables.domains.end(),
                [] (const auto & a, const auto & b) {
                    return a.second.size() < b.second.size();
                    });
    }

    auto learn_greedy(const std::pair<Graph, Graph> & graphs,
            const VariablesStack & variables_stack, unsigned stack_level, LearnedNogoods & learned_nogoods,
            const unsigned failed_variable)
    {
        FalseImplication nogood;

        auto unseen = variables_stack.variables.at(0).domains.find(failed_variable)->second;
        std::vector<std::pair<unsigned, std::set<unsigned> > > disallowed_by_level(stack_level + 1);

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
            auto & d = *std::max_element(disallowed_by_level.rbegin(), disallowed_by_level.rend(),
                    [] (const auto & a, const auto & b) {
                        return a.second.size() < b.second.size();
                    });

            if (d.second.empty())
                throw 0;

            bool reduced = false;
            for (auto & v : d.second)
                if (unseen.count(v)) {
                    reduced = true;
                    unseen.erase(v);
                }

            if (reduced)
                nogood.emplace_back(variables_stack.variables.at(d.first).assignment);

            auto to_remove = d.second;
            for (auto & l : disallowed_by_level) {
                for (auto & r : to_remove)
                    l.second.erase(r);
            }
        }

        learned_nogoods.insert(nogood);
    }

    auto current_state_is_nogood(
            VariablesStack & variables_stack, unsigned stack_level,
            LearnedNogoods & learned_nogoods) -> bool
    {
        for (auto & nogood : learned_nogoods) {
            bool contradicted = false;
            for (auto & a : nogood) {
                bool found = false;
                for (unsigned d = 1 ; d <= stack_level ; ++d)
                    if (variables_stack.variables.at(d).assignment == a) {
                        found = true;
                        break;
                    }

                if (! found) {
                    contradicted = true;
                    break;
                }
            }

            if (! contradicted)
                return true;
        }

        return false;
    }

    auto solve(const std::pair<Graph, Graph> & graphs, const Params & params, Result & result,
            VariablesStack & variables_stack, unsigned stack_level,
            LearnedNogoods & learned_nogoods) -> bool
    {
        if (*params.abort)
            return false;

        if (current_state_is_nogood(variables_stack, stack_level, learned_nogoods))
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

        for (const auto & t : branch_variable->second) {
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

            if (solve(graphs, params, result, variables_stack, stack_level + 1, learned_nogoods))
                return true;
        }

        return false;
    }
}

auto simple_subgraph_isomorphism(const std::pair<Graph, Graph> & graphs, const Params & params) -> Result
{
    Result result;

    VariablesStack variables_stack(graphs.first.size(), graphs.second.size());
    LearnedNogoods learned_nogoods;

    initialise_variables(graphs, params, variables_stack.variables.at(0));
    if (! solve(graphs, params, result, variables_stack, 0, learned_nogoods))
        result.isomorphism.clear();

    std::map<unsigned, unsigned> clauses;
    for (auto & n : learned_nogoods)
        clauses[n.size()]++;

    std::cerr << "Learned " << learned_nogoods.size() << ":";
    for (auto & c : clauses)
        std::cerr << " " << c.first << "=" << c.second;
    std::cerr << std::endl;

    return result;
}

