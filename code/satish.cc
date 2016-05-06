/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "satish.hh"

#include <functional>
#include <list>
#include <map>
#include <vector>
#include <utility>

#include <boost/dynamic_bitset.hpp>

using std::greater;
using std::list;
using std::map;
using std::pair;
using std::vector;

using bitset = boost::dynamic_bitset<>;

namespace
{
    struct Domain
    {
        unsigned v;
        bitset values;
    };

    using Domains = vector<Domain>;

    struct Assignments
    {
        vector<pair<unsigned, unsigned> > trail;

        auto push(unsigned a, unsigned b) -> void
        {
            trail.emplace_back(a, b);
        }

        auto pop() -> void
        {
            trail.pop_back();
        }

        auto store_to(map<int, int> & m) -> void
        {
            for (auto & t : trail)
                m.insert(t);
        }
    };

    struct SIP
    {
        const Params & params;

        Result result;

        list<pair<vector<bitset>, vector<bitset> > > adjacency_constraints;
        vector<unsigned> pattern_degrees, target_degrees;

        Domains initial_domains;

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

        auto select_branch_domain(const Domains & domains) -> const Domain &
        {
            return *min_element(domains.begin(), domains.end(), [&] (const auto & a, const auto & b) {
                    int ac = a.values.count();
                    int bc = b.values.count();
                    return (ac < bc)
                        || (ac == bc && pattern_degrees[a.v] > pattern_degrees[b.v])
                        || (ac == bc && pattern_degrees[a.v] == pattern_degrees[b.v] && a.v < b.v);
                    });
        }

        auto solve(
                const Domains & domains,
                const Domain & branch_domain,
                Assignments & assignments) -> bool
        {
            if (*params.abort)
                return false;

            ++result.nodes;

            vector<unsigned> branch_values;
            for (auto branch_value = branch_domain.values.find_first() ;
                    branch_value != bitset::npos ;
                    branch_value = branch_domain.values.find_next(branch_value))
                branch_values.push_back(branch_value);

            sort(branch_values.begin(), branch_values.end(), [&] (const auto & a, const auto & b) {
                    return target_degrees[a] < target_degrees[b] || (target_degrees[a] == target_degrees[b] && a < b);
                    });

            for (auto & branch_value : branch_values) {
                assignments.push(branch_domain.v, branch_value);

                Domains new_domains;
                new_domains.reserve(domains.size() - 1);
                for (auto & d : domains) {
                    if (d.v == branch_domain.v)
                        continue;

                    new_domains.emplace_back(Domain{ unsigned(d.v), d.values });
                }

                if (new_domains.empty()) {
                    assignments.store_to(result.isomorphism);
                    return true;
                }

                for (auto & d : new_domains) {
                    // injectivity
                    d.values.reset(branch_value);

                    // adjacency
                    for (auto & c : adjacency_constraints)
                        if (c.first[branch_domain.v].test(d.v))
                            d.values &= c.second[branch_value];
                }

                auto & new_branch_domain = select_branch_domain(new_domains);
                if (! new_branch_domain.values.none()) {
                    if (solve(new_domains, new_branch_domain, assignments))
                        return true;
                }

                // restore assignments
                assignments.pop();
            }

            return false;
        }

        auto run()
        {
            Assignments assignments;

            auto & branch_domain = select_branch_domain(initial_domains);

            if (! branch_domain.values.none())
                solve(initial_domains, branch_domain, assignments);
        }
    };
}

auto satish_subgraph_isomorphism(const pair<Graph, Graph> & graphs, const Params & params) -> Result
{
    SIP sip(params, graphs.first, graphs.second);

    sip.run();

    return sip.result;
}

