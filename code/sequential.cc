/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "sequential.hh"

#include <map>
#include <set>
#include <list>
#include <boost/dynamic_bitset.hpp>
#include <boost/range/adaptor/reversed.hpp>

#include <iostream>

using std::map;
using std::set;
using std::vector;
using std::list;
using std::to_string;
using std::make_pair;
using std::pair;
using std::move;

using std::cerr;
using std::endl;

using boost::adaptors::reverse;

using bitset = boost::dynamic_bitset<>;

namespace
{
    struct Domain
    {
        unsigned v;
        bitset values;
    };

    using Domains = vector<Domain>;

    using Assignment = pair<unsigned, unsigned>;
    using Assignments = vector<Assignment>;

    struct LearnedClauses
    {
        list<vector<Assignment> > nogoods;

        auto add(vector<Assignment> && clause) -> void
        {
            nogoods.push_back(move(clause));
        }

        auto apply_forced_assignment(Domains & domains, const Assignment & a)
        {
            for (auto & d : domains)
                if (d.v == a.first) {
                    d.values.reset(a.second);
                    return;
                }

            throw 0;
        }

        enum nogood_knowledge { irrelevant, totally_nogood, single_assignment_forced };

        auto reduce_assigned_domains(const vector<Assignment> & assignments, Domains & domains) -> bool
        {
            for (auto & nogood : nogoods) {
                Assignment forced_assignment;
                switch (what_does_nogood_tell_us(nogood, assignments, forced_assignment)) {
                    case totally_nogood:
                        return false;
                    case single_assignment_forced:
                        apply_forced_assignment(domains, forced_assignment);
                        break;
                    case irrelevant:
                        break;
                }
            }

            return true;
        }

        auto apply_units(const vector<Assignment> & assignments, unsigned branch_variable,
                bitset & supported_values, set<Assignment> & used_assignments) -> void
        {
            for (auto & nogood : nogoods) {
                Assignment forced_assignment;
                switch (what_does_nogood_tell_us(nogood, assignments, forced_assignment)) {
                    case totally_nogood:
                        throw 0;
                    case single_assignment_forced:
                        if (forced_assignment.first == branch_variable) {
                            used_assignments.insert(nogood.begin(), nogood.end());
                            supported_values.reset(forced_assignment.second);
                        }
                        break;
                    case irrelevant:
                        break;
                }
            }
        }

        enum contained_in_assignment { contained, contradicts, missing };

        auto what_does_nogood_tell_us(const vector<Assignment> & nogood, const vector<Assignment> & assignments,
                Assignment & forced) -> nogood_knowledge
        {
            unsigned n_missing = 0;
            for (auto & n : nogood) {
                switch (contained_in_assignments(n, assignments)) {
                    case contained:
                        break;
                    case contradicts:
                        return irrelevant;
                    case missing:
                        ++n_missing;
                        forced = n;
                        break;
                }
                if (n_missing > 1)
                    break;
            }

            if (0 == n_missing)
                return totally_nogood;
            else if (1 == n_missing)
                return single_assignment_forced;
            else
                return irrelevant;
        }

        auto contained_in_assignments(const Assignment & n, const vector<Assignment> & assignments) -> contained_in_assignment
        {
            for (auto & a : assignments)
                if (a == n)
                    return contained;
                else if (a.first == n.first)
                    return contradicts;

            return missing;
        }
    };

    struct SIP
    {
        const Params & params;

        Result result;
        map<unsigned, unsigned> fail_depths;

        list<pair<vector<bitset>, vector<bitset> > > adjacency_constraints;

        Domains initial_domains;

        LearnedClauses learned_clauses;

        SIP(const Params & k, const Graph & pattern, const Graph & target) :
            params(k),
            initial_domains(pattern.size())
        {
            // build up distance 1 adjacency bitsets
            add_adjacency_constraints(pattern, target);

            // build up initial domains
            for (unsigned p = 0 ; p < pattern.size() ; ++p) {
                initial_domains[p].v = p;
                initial_domains[p].values = bitset(target.size());

                for (unsigned t = 0 ; t < target.size() ; ++t) {
                    bool ok = true;
                    for (auto & c : adjacency_constraints)
                        if (! (c.first[p][p] == c.second[t][t] && c.first[p].count() <= c.second[t].count())) {
                            ok = false;
                            break;
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
                auto & d2 = *adjacency_constraints.insert(
                        adjacency_constraints.end(), make_pair(vector<bitset>(), vector<bitset>()));
                build_d2_adjacency(pattern, d2.first);
                build_d2_adjacency(target, d2.second);
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

        auto build_d2_adjacency(const Graph & graph, vector<bitset> & adj) const -> void
        {
            adj.resize(graph.size());
            for (unsigned t = 0 ; t < graph.size() ; ++t) {
                adj[t] = bitset(graph.size(), 0);
                for (unsigned u = 0 ; u < graph.size() ; ++u)
                    if (graph.adjacent(t, u))
                        for (unsigned v = 0 ; v < graph.size() ; ++v)
                            if (t != v && graph.adjacent(u, v))
                                adj[t].set(v);
            }
        }

        auto select_branch_domain(const Domains & domains) -> const Domain &
        {
            return *min_element(domains.begin(), domains.end(), [] (const auto & a, const auto & b) {
                    return a.values.count() < b.values.count();
                    });
        }

        auto learn_from_wipeout(const unsigned failed_variable, const Assignments & assignments) -> void
        {
            bitset to_explain = initial_domains[failed_variable].values;
            vector<Assignment> new_nogood;
            set<Assignment> used_in_new_nogood;

            for (auto & assignment : reverse(assignments)) {
                if (to_explain.none())
                    break;

                new_nogood.push_back(assignment);

                bitset supported_values = to_explain;

                for (auto & c : adjacency_constraints)
                    if (c.first[assignment.first].test(failed_variable))
                        supported_values &= c.second[assignment.second];

                if (supported_values != to_explain) {
                    supported_values.reset(assignment.second);
                    used_in_new_nogood.insert(assignment);
                    learned_clauses.apply_units(new_nogood, failed_variable, supported_values, used_in_new_nogood);
                    to_explain &= supported_values;
                }
                else
                    new_nogood.pop_back();
            }

            for (auto & assignment : reverse(assignments)) {
                if (used_in_new_nogood.count(assignment))
                    continue;

                if (to_explain.none())
                    break;

                new_nogood.push_back(assignment);

                bitset supported_values = to_explain;

                supported_values.reset(assignment.second);

                for (auto & c : adjacency_constraints)
                    if (c.first[assignment.first].test(failed_variable))
                        supported_values &= c.second[assignment.second];

                if (supported_values != to_explain)
                    used_in_new_nogood.insert(assignment);

                learned_clauses.apply_units(new_nogood, failed_variable, supported_values, used_in_new_nogood);
                to_explain &= supported_values;
            }

            if (! to_explain.none()) {
                cerr << "Oops: couldn't explain failure: to explain " << failed_variable << " contains " << to_explain.count()
                    << " of " << initial_domains[failed_variable].values.count() << ":";
                for (unsigned v = 0 ; v < to_explain.size() ; ++v)
                    if (to_explain[v])
                        cerr << " " << v;
                cerr << endl;
            }
            else {
                vector<Assignment> reduced_new_nogood(used_in_new_nogood.begin(), used_in_new_nogood.end());
                learned_clauses.add(move(reduced_new_nogood));
            }
        }

        auto solve(const Domains & domains, const Assignments & assignments) -> bool
        {
            if (*params.abort)
                return false;

            ++result.nodes;

            auto & branch_domain = select_branch_domain(domains);

            if (branch_domain.values.none()) {
                // domain wipeout
                ++fail_depths[assignments.size()];

                if (params.learn)
                    learn_from_wipeout(branch_domain.v, assignments);

                return false;
            }
            // else if (branch_domain.values.count() == 1) {
                // entailed by previous assignments?
            // }

            for (auto branch_value = branch_domain.values.find_first() ;
                    branch_value != bitset::npos ;
                    branch_value = branch_domain.values.find_next(branch_value)) {
                auto new_assignments = assignments;
                new_assignments.emplace_back(branch_domain.v, branch_value);

                Domains new_domains;
                new_domains.reserve(domains.size() - 1);
                for (auto & d : domains) {
                    if (d.v == branch_domain.v)
                        continue;

                    auto new_values = d.values;

                    // injectivity
                    new_values.reset(branch_value);

                    // adjacency
                    for (auto & c : adjacency_constraints)
                        if (c.first[branch_domain.v].test(d.v))
                            new_values &= c.second[branch_value];

                    new_domains.emplace_back(Domain{ unsigned(d.v), new_values });
                }

                if (new_domains.empty()) {
                    for (auto & a : new_assignments)
                        result.isomorphism.emplace(a.first, a.second);
                    return true;
                }
                else {
                    if (learned_clauses.reduce_assigned_domains(new_assignments, new_domains))
                        if (solve(new_domains, new_assignments))
                            return true;
                }
            }

            return false;
        }

        auto run()
        {
            solve(initial_domains, {});

            for (auto & d : fail_depths)
                result.stats["D" + to_string(d.first)] = to_string(d.second);

            map<unsigned, unsigned> learned_clause_sizes;
            for (auto & d : learned_clauses.nogoods)
                learned_clause_sizes[d.size()]++;

            for (auto & d : learned_clause_sizes)
                result.stats["L" + to_string(d.first)] = to_string(d.second);
        }
    };
}

auto sequential_subgraph_isomorphism(const pair<Graph, Graph> & graphs, const Params & params) -> Result
{
    SIP sip(params, graphs.first, graphs.second);

    sip.run();

    return sip.result;
}

