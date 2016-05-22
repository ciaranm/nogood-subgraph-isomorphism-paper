/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "satish.hh"

#include <algorithm>
#include <functional>
#include <list>
#include <map>
#include <tuple>
#include <utility>
#include <vector>

#include <iostream>

#include <boost/dynamic_bitset.hpp>

using std::find_if;
using std::get;
using std::greater;
using std::list;
using std::make_pair;
using std::map;
using std::pair;
using std::to_string;
using std::tuple;
using std::unique;
using std::vector;

using std::cerr;
using std::endl;

using bitset = boost::dynamic_bitset<>;

namespace
{
    struct Domain
    {
        unsigned v;
        bool fixed;
        bitset values;
        vector<unsigned> was_modified_by;
    };

    using Domains = vector<Domain>;

    struct Assignments
    {
        vector<tuple<unsigned, unsigned, bool> > trail;

        auto push_branch(unsigned a, unsigned b) -> void
        {
            trail.emplace_back(a, b, true);
        }

        auto push_implication(unsigned a, unsigned b) -> void
        {
            if (trail.end() == find_if(trail.begin(), trail.end(), [&] (const auto & x) {
                        return get<0>(x) == a && get<1>(x) == b;
                        }))
                trail.emplace_back(a, b, false);
        }

        auto pop() -> void
        {
            while ((! trail.empty()) && (! get<2>(trail.back())))
                trail.pop_back();

            if (! trail.empty())
                trail.pop_back();
        }

        auto store_to(map<int, int> & m) -> void
        {
            for (auto & t : trail) {
                m.emplace(get<0>(t), get<1>(t));
            }
        }
    };

    using LearnedClauses = list<pair<vector<pair<unsigned, unsigned> >, bool> >;

    struct SIP
    {
        const Params & params;

        Result result;

        list<pair<vector<bitset>, vector<bitset> > > adjacency_constraints;
        vector<unsigned> pattern_degrees, target_degrees;

        Domains initial_domains;
        LearnedClauses learned_clauses;
        map<pair<unsigned, unsigned>, unsigned> fail_depths;

        SIP(const Params & k, const Graph & pattern, const Graph & target) :
            params(k),
            pattern_degrees(pattern.size()),
            target_degrees(target.size()),
            initial_domains(pattern.size())
        {
            // build up distance 1 adjacency bitsets
            add_adjacency_constraints(pattern, target);

            for (unsigned p = 0 ; p < pattern.size() ; ++p)
                pattern_degrees[p] = pattern.degree(p);

            for (unsigned t = 0 ; t < target.size() ; ++t)
                target_degrees[t] = target.degree(t);

            vector<vector<vector<unsigned> > > p_nds(adjacency_constraints.size());
            vector<vector<vector<unsigned> > > t_nds(adjacency_constraints.size());

            for (unsigned p = 0 ; p < pattern.size() ; ++p) {
                unsigned cn = 0;
                for (auto & c : adjacency_constraints) {
                    p_nds[cn].resize(pattern.size());
                    for (unsigned q = 0 ; q < pattern.size() ; ++q)
                        if (c.first[p][q])
                            p_nds[cn][p].push_back(c.first[q].count());
                    sort(p_nds[cn][p].begin(), p_nds[cn][p].end(), greater<unsigned>());
                    ++cn;
                }
            }

            for (unsigned t = 0 ; t < target.size() ; ++t) {
                unsigned cn = 0;
                for (auto & c : adjacency_constraints) {
                    t_nds[cn].resize(target.size());
                    for (unsigned q = 0 ; q < target.size() ; ++q)
                        if (c.second[t][q])
                            t_nds[cn][t].push_back(c.second[q].count());
                    sort(t_nds[cn][t].begin(), t_nds[cn][t].end(), greater<unsigned>());
                    ++cn;
                }
            }

            // build up initial domains
            for (unsigned p = 0 ; p < pattern.size() ; ++p) {
                initial_domains[p].v = p;
                initial_domains[p].values = bitset(target.size());
                initial_domains[p].fixed = false;

                for (unsigned t = 0 ; t < target.size() ; ++t) {
                    bool ok = true;
                    for (auto & c : adjacency_constraints) {
                        if (! (c.first[p][p] == c.second[t][t] && c.first[p].count() <= c.second[t].count())) {
                            ok = false;
                            break;
                        }
                    }

                    for (unsigned cn = 0 ; cn < adjacency_constraints.size() && ok ; ++cn) {
                        for (unsigned i = 0 ; i < p_nds[cn][p].size() ; ++i) {
                            if (t_nds[cn][t][i] < p_nds[cn][p][i]) {
                                ok = false;
                                break;
                            }
                        }
                    }

                    if (ok)
                        initial_domains[p].values.set(t);
                }
            }
        }

        auto add_adjacency_constraints(const Graph & pattern, const Graph & target) -> void
        {
            auto & d1 = *adjacency_constraints.insert(
                    adjacency_constraints.end(), make_pair(vector<bitset>(), vector<bitset>()));
            build_d1_adjacency(pattern, d1.first);
            build_d1_adjacency(target, d1.second);

            if (params.d2graphs) {
                auto & d21 = *adjacency_constraints.insert(
                        adjacency_constraints.end(), make_pair(vector<bitset>(), vector<bitset>()));
                auto & d22 = *adjacency_constraints.insert(
                        adjacency_constraints.end(), make_pair(vector<bitset>(), vector<bitset>()));
                auto & d23 = *adjacency_constraints.insert(
                        adjacency_constraints.end(), make_pair(vector<bitset>(), vector<bitset>()));

                build_d2_adjacency(pattern, d21.first, d22.first, d23.first);
                build_d2_adjacency(target, d21.second, d22.second, d23.second);
            }
        }

        auto build_d1_adjacency(const Graph & graph, vector<bitset> & adj) const -> void
        {
            adj.resize(graph.size());
            for (unsigned t = 0 ; t < graph.size() ; ++t) {
                adj[t] = bitset(graph.size(), 0);
                for (unsigned u = 0 ; u < graph.size() ; ++u)
                    if (graph.adjacent(t, u))
                        adj[t].set(u);
            }
        }

        auto build_d2_adjacency(const Graph & graph,
                vector<bitset> & adj1,
                vector<bitset> & adj2,
                vector<bitset> & adj3) const -> void
        {
            adj1.resize(graph.size());
            adj2.resize(graph.size());
            adj3.resize(graph.size());
            for (unsigned t = 0 ; t < graph.size() ; ++t) {
                adj1[t] = bitset(graph.size(), 0);
                adj2[t] = bitset(graph.size(), 0);
                adj3[t] = bitset(graph.size(), 0);
                for (unsigned u = 0 ; u < graph.size() ; ++u)
                    if (graph.adjacent(t, u))
                        for (unsigned v = 0 ; v < graph.size() ; ++v)
                            if (t != v && graph.adjacent(u, v)) {
                                if (adj2[t].test(v))
                                    adj3[t].set(v);
                                else if (adj1[t].test(v))
                                    adj2[t].set(v);
                                else
                                    adj1[t].set(v);
                            }
            }
        }

        auto select_branch_domain(Domains & domains) -> Domains::iterator
        {
            auto best = domains.end();

            for (auto d = domains.begin() ; d != domains.end() ; ++d) {
                if (d->fixed)
                    continue;

                if (best == domains.end())
                    best = d;
                else {
                    int best_c = best->values.count();
                    int d_c = d->values.count();

                    if (d_c < best_c)
                        best = d;
                    else if (d_c == best_c) {
                        if (pattern_degrees[d->v] > pattern_degrees[best->v])
                            best = d;
                        else if (pattern_degrees[d->v] == pattern_degrees[best->v] && d->v < best->v)
                            best = d;
                    }
                }
            }

            return best;
        }

        auto select_unit_domain(Domains & domains) -> Domains::iterator
        {
            return find_if(domains.begin(), domains.end(), [] (const auto & a) {
                    return (! a.fixed) && 1 == a.values.count();
                    });
        }

        auto unit_propagate(Domains & domains, Assignments & assignments) -> LearnedClauses::iterator
        {
            while (! domains.empty()) {
                auto unit_domain_iter = select_unit_domain(domains);

                if (unit_domain_iter == domains.end())
                    break;

                auto unit_domain_v = unit_domain_iter->v;
                auto unit_domain_value = unit_domain_iter->values.find_first();
                unit_domain_iter->fixed = true;

                assignments.push_implication(unit_domain_v, unit_domain_value);

                for (auto & d : domains) {
                    if (d.fixed)
                        continue;

                    auto old_domain_size = d.values.count();

                    // injectivity
                    d.values.reset(unit_domain_value);

                    // adjacency
                    for (auto & c : adjacency_constraints)
                        if (c.first[unit_domain_v].test(d.v))
                            d.values &= c.second[unit_domain_value];

                    auto new_domain_size = d.values.count();

                    if (new_domain_size != old_domain_size)
                        d.was_modified_by.emplace_back(assignments.trail.size() - 1);

                    if (0 == new_domain_size) {
                        vector<pair<unsigned, unsigned> > reason;
                        for (auto & m : d.was_modified_by)
                            reason.emplace_back(get<0>(assignments.trail.at(m)), get<1>(assignments.trail.at(m)));

                        return learned_clauses.insert(learned_clauses.end(), make_pair(move(reason), false));
                    }
                }
            }

            return learned_clauses.end();
        }

        auto solve(
                Domains & domains,
                Assignments & assignments) -> pair<bool, LearnedClauses::iterator>
        {
            if (*params.abort)
                return make_pair(true, learned_clauses.end());

            ++result.nodes;

            auto unit_propagation = unit_propagate(domains, assignments);
            if (unit_propagation != learned_clauses.end()) {
                ++fail_depths[make_pair(assignments.trail.size(), count_if(assignments.trail.begin(), assignments.trail.end(),
                            [] (const auto & a) { return get<2>(a); }))];
                return make_pair(false, unit_propagation);
            }

            auto branch_domain = select_branch_domain(domains);

            if (domains.end() == branch_domain) {
                assignments.store_to(result.isomorphism);
                return make_pair(true, learned_clauses.end());
            }

            vector<unsigned> branch_values;
            for (auto branch_value = branch_domain->values.find_first() ;
                    branch_value != bitset::npos ;
                    branch_value = branch_domain->values.find_next(branch_value))
                branch_values.push_back(branch_value);

            sort(branch_values.begin(), branch_values.end(), [&] (const auto & a, const auto & b) {
                    return target_degrees[a] < target_degrees[b] || (target_degrees[a] == target_degrees[b] && a < b);
                    });

            vector<pair<unsigned, unsigned> > full_reason;

            for (auto & branch_value : branch_values) {
                assignments.push_branch(branch_domain->v, branch_value);

                Domains new_domains;
                new_domains.reserve(domains.size());
                for (auto & d : domains) {
                    if (d.fixed)
                        continue;

                    if (d.v == branch_domain->v) {
                        bitset just_branch_value = d.values;
                        just_branch_value.reset();
                        just_branch_value.set(branch_value);
                        new_domains.emplace_back(Domain{ unsigned(d.v), false, just_branch_value, d.was_modified_by });
                    }
                    else
                        new_domains.emplace_back(Domain{ unsigned(d.v), false, d.values, d.was_modified_by });
                }

                auto solution = solve(new_domains, assignments);
                if (solution.first)
                    return solution;
                else
                    full_reason.insert(full_reason.end(), solution.second->first.begin(), solution.second->first.end());

                // restore assignments
                assignments.pop();
            }

            for (auto & m : branch_domain->was_modified_by)
                full_reason.emplace_back(get<0>(assignments.trail.at(m)), get<1>(assignments.trail.at(m)));

            sort(full_reason.begin(), full_reason.end());
            full_reason.erase(unique(full_reason.begin(), full_reason.end()), full_reason.end());

            return make_pair(false, learned_clauses.insert(learned_clauses.end(), make_pair(move(full_reason), true)));
        }

        auto run()
        {
            Assignments assignments;

            // eliminate isolated vertices?

            solve(initial_domains, assignments);

            for (auto & d : fail_depths)
                result.stats["D" + to_string(d.first.first) + "/" + to_string(d.first.second)] = to_string(d.second);

            map<unsigned, unsigned> learned_clause_sizes_w, learned_clause_sizes_b;
            for (auto & d : learned_clauses)
                if (d.second)
                    learned_clause_sizes_b[d.first.size()]++;
                else
                    learned_clause_sizes_w[d.first.size()]++;

            for (auto & d : learned_clause_sizes_b)
                result.stats["B" + to_string(d.first)] = to_string(d.second);

            for (auto & d : learned_clause_sizes_w)
                result.stats["A" + to_string(d.first)] = to_string(d.second);
        }
    };
}

auto satish_subgraph_isomorphism(const pair<Graph, Graph> & graphs, const Params & params) -> Result
{
    SIP sip(params, graphs.first, graphs.second);

    sip.run();

    return sip.result;
}

