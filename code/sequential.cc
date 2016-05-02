/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#include "sequential.hh"

#include <map>
#include <unordered_map>
#include <set>
#include <list>
#include <limits>
#include <boost/dynamic_bitset.hpp>
#include <boost/range/adaptor/reversed.hpp>
#include <boost/functional/hash.hpp>

#include <iostream>
#include <ostream>
#include <sstream>

using std::map;
using std::unordered_map;
using std::set;
using std::vector;
using std::list;
using std::to_string;
using std::make_pair;
using std::pair;
using std::move;
using std::numeric_limits;

using std::cerr;
using std::endl;
using std::ostream;
using std::stringstream;

using boost::adaptors::reverse;

using bitset = boost::dynamic_bitset<>;

template <typename T, typename U>
ostream & operator<< (ostream & s, const pair<T, U> & v)
{
    s << "(" << v.first << ", " << v.second << ")";
    return s;
}

template <typename T>
ostream & operator<< (ostream & s, const vector<T> & v)
{
    s << "[";
    bool first = true;
    for (auto & e : v) {
        if (! first)
            s << ", ";
        s << e;
        first = false;
    }
    s << "]";
    return s;
}

template <typename T>
ostream & operator<< (ostream & s, const list<T *> & v)
{
    s << "[";
    bool first = true;
    for (auto & e : v) {
        if (! first)
            s << ", ";
        s << *e;
        first = false;
    }
    s << "]";
    return s;
}

namespace
{
    constexpr unsigned unassigned = numeric_limits<unsigned>::max();

    struct Domain
    {
        unsigned v;
        bitset values;
    };

    using Domains = vector<Domain>;

    using Assignment = pair<unsigned, unsigned>;
    using Assignments = vector<Assignment>;

    struct Nogood;

    using NogoodList = list<Nogood *>;

    struct Nogood
    {
        NogoodList::iterator active_list_position;
        NogoodList::iterator spent_list_position;
        NogoodList::iterator first_list_position;
        NogoodList::iterator second_list_position;
        vector<Assignment> assignments;
    };

    struct LearnedClauses
    {
        NogoodList active, spent_clauses;
        unordered_map<Assignment, NogoodList, boost::hash<Assignment> > watches;

        list<Nogood> nogood_store;

        auto add(vector<Assignment> && clause) -> void
        {
            auto nogood_position = nogood_store.insert(nogood_store.end(), Nogood{ });
            nogood_position->assignments = move(clause);

            auto active_position = active.insert(active.end(), &*nogood_position);
            nogood_position->active_list_position = active_position;
        }

        auto apply_forced_assignment(Domains & domains, const Assignment & a)
        {
            for (auto & d : domains)
                if (d.v == a.first) {
                    d.values.reset(a.second);
                    return;
                }

            cerr << "couldn't apply forced assignment " << a << endl;
            throw 0;
        }

        enum class NogoodKnowledge { irrelevant, totally_nogood, single_assignment_forced, contradicting };

        auto propagate_assignment(
                const Assignment & new_assignment,
                const vector<unsigned> & assignments_map,
                Domains & domains) -> bool
        {
            // for each assignment that doesn't have a home yet...
            if (! propagate_assignment_using_clause_list(active, assignments_map, domains))
                return false;

            // and for each assignment on the watch list...
            auto watched_list = watches.find(new_assignment);
            if (watched_list != watches.end())
                if (! propagate_assignment_using_clause_list(watched_list->second, assignments_map, domains))
                    return false;

            return true;
        }

        auto propagate_assignment_using_clause_list(
                NogoodList & clause_list,
                const vector<unsigned> & assignments_map,
                Domains & domains) -> bool
        {
            for (auto nogood_iterator = clause_list.begin(), nogood_end = clause_list.end() ; nogood_iterator != nogood_end ; ) {
                Assignment * first_mismatch = nullptr, * second_mismatch = nullptr;
                switch (what_does_nogood_tell_us(**nogood_iterator, assignments_map, first_mismatch, second_mismatch)) {
                    case NogoodKnowledge::totally_nogood:
                        return false;

                    case NogoodKnowledge::single_assignment_forced:
                        {
                            apply_forced_assignment(domains, *first_mismatch);
                            Nogood * nogood = *nogood_iterator++;

                            if (nogood->assignments.size() >= 2) {
                                if (nogood->active_list_position != active.end()) {
                                    active.erase(nogood->active_list_position);
                                    nogood->active_list_position = active.end();
                                }
                                else {
                                    watches[nogood->assignments.at(0)].erase(nogood->first_list_position);
                                    watches[nogood->assignments.at(1)].erase(nogood->second_list_position);
                                }

                                nogood->spent_list_position = spent_clauses.insert(spent_clauses.begin(), nogood);
                            }
                        }
                        break;

                    case NogoodKnowledge::contradicting:
                        ++nogood_iterator;
                        break;

                    case NogoodKnowledge::irrelevant:
                        {
                            Nogood * nogood = *nogood_iterator++;

                            // move to its new homes
                            if (nogood->assignments.size() >= 2) {
                                if (nogood->active_list_position != active.end()) {
                                    active.erase(nogood->active_list_position);
                                    nogood->active_list_position = active.end();
                                }
                                else {
                                    watches[nogood->assignments.at(0)].erase(nogood->first_list_position);
                                    watches[nogood->assignments.at(1)].erase(nogood->second_list_position);
                                }

                                swap(nogood->assignments.at(0), *first_mismatch);
                                swap(nogood->assignments.at(1), *second_mismatch);
                                auto & first_list = watches[nogood->assignments.at(0)];
                                nogood->first_list_position = first_list.insert(first_list.end(), nogood);
                                auto & second_list = watches[nogood->assignments.at(1)];
                                nogood->second_list_position = second_list.insert(second_list.end(), nogood);
                            }
                        }
                        break;
                }
            }

            return true;
        }

        auto apply_units(
                const vector<Assignment> &,
                const vector<unsigned> & assignments_map,
                unsigned branch_variable,
                bitset & to_explain,
                set<Assignment> & used_assignments) -> void
        {
            for (auto & nogood : active)
                if (apply_this_nogood_to_units(*nogood, assignments_map, branch_variable, to_explain, used_assignments)) {
                }
            for (auto & nogood : spent_clauses)
                if (apply_this_nogood_to_units(*nogood, assignments_map, branch_variable, to_explain, used_assignments)) {
                }
        }

        auto apply_this_nogood_to_units(
                Nogood & nogood,
                const vector<unsigned> & assignments_map,
                unsigned branch_variable,
                bitset & to_explain,
                set<Assignment> & used_assignments) -> bool
        {
            Assignment * first_mismatch = nullptr, * second_mismatch = nullptr;
            switch (what_does_nogood_tell_us(nogood, assignments_map, first_mismatch, second_mismatch)) {
                case NogoodKnowledge::totally_nogood:
                    cerr << "totally nogood " << nogood.assignments << " on branch " << assignments_map << endl;
                    throw 0;

                case NogoodKnowledge::single_assignment_forced:
                    if (first_mismatch->first == branch_variable && to_explain.test(first_mismatch->second)) {
                        for (auto & a : nogood.assignments)
                            if (a.first != branch_variable)
                                used_assignments.insert(a);
                        to_explain.reset(first_mismatch->second);
                        return true;
                    }
                    break;

                case NogoodKnowledge::contradicting:
                    break;

                case NogoodKnowledge::irrelevant:
                    break;
            }

            return false;
        }

        enum class ContainedInAssignment { contained, contradicts, missing };

        auto what_does_nogood_tell_us(
                Nogood & nogood,
                const vector<unsigned> & assignments_map,
                Assignment * & first_mismatch,
                Assignment * & second_mismatch) -> NogoodKnowledge
        {
            unsigned n_missing = 0;
            for (auto & n : nogood.assignments) {
                switch (contained_in_assignments(n, assignments_map)) {
                    case ContainedInAssignment::contained:
                        break;
                    case ContainedInAssignment::contradicts:
                        first_mismatch = &n;
                        return NogoodKnowledge::contradicting;
                    case ContainedInAssignment::missing:
                        ++n_missing;
                        second_mismatch = first_mismatch;
                        first_mismatch = &n;
                        break;
                }
                if (n_missing > 1)
                    break;
            }

            if (0 == n_missing)
                return NogoodKnowledge::totally_nogood;
            else if (1 == n_missing)
                return NogoodKnowledge::single_assignment_forced;
            else
                return NogoodKnowledge::irrelevant;
        }

        auto contained_in_assignments(
                const Assignment & n,
                const vector<unsigned> & assignments_map) -> ContainedInAssignment
        {
            if (assignments_map[n.first] == unassigned)
                return ContainedInAssignment::missing;
            else if (assignments_map[n.first] == n.second)
                return ContainedInAssignment::contained;
            else
                return ContainedInAssignment::contradicts;
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

        auto learn_from_wipeout(const unsigned failed_variable, const Assignments & assignments,
                const vector<unsigned> & assignments_map) -> void
        {
            bitset to_explain = initial_domains[failed_variable].values;
            vector<Assignment> new_nogood;

            // try to explain just using distance constraints
            for (auto & assignment : reverse(assignments)) {
                if (to_explain.none())
                    break;

                bitset still_to_explain = to_explain;

                for (auto & c : adjacency_constraints)
                    if (c.first[assignment.first].test(failed_variable))
                        still_to_explain &= c.second[assignment.second];

                if (still_to_explain != to_explain) {
                    still_to_explain.reset(assignment.second);
                    to_explain &= still_to_explain;
                    new_nogood.push_back(assignment);
                }
            }

            // we might need more than distances...
            for (auto & assignment : reverse(assignments)) {
                if (to_explain.none())
                    break;

                bitset still_to_explain = to_explain;

                still_to_explain.reset(assignment.second);

                for (auto & c : adjacency_constraints)
                    if (c.first[assignment.first].test(failed_variable))
                        still_to_explain &= c.second[assignment.second];

                if (still_to_explain != to_explain) {
                    to_explain &= still_to_explain;
                    if (new_nogood.end() == find(new_nogood.begin(), new_nogood.end(), assignment))
                        new_nogood.push_back(assignment);
                }
            }

            if (! to_explain.none()) {
                bitset still_to_explain = to_explain;
                set<Assignment> used_assignments;
                learned_clauses.apply_units(assignments, assignments_map, failed_variable, still_to_explain, used_assignments);
                to_explain &= still_to_explain;

                for (auto & a : used_assignments)
                    if (new_nogood.end() == find(new_nogood.begin(), new_nogood.end(), a))
                        new_nogood.push_back(a);
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
                learned_clauses.add(move(new_nogood));
            }
        }

        auto solve(
                const Domains & domains,
                const Assignments & assignments,
                const vector<unsigned> & assignments_map) -> bool
        {
            if (*params.abort)
                return false;

            ++result.nodes;

            auto & branch_domain = select_branch_domain(domains);

            if (branch_domain.values.none()) {
                // domain wipeout
                ++fail_depths[assignments.size()];

                if (params.learn)
                    learn_from_wipeout(branch_domain.v, assignments, assignments_map);

                return false;
            }
            // else if (branch_domain.values.count() == 1) {
                // entailed by previous assignments?
            // }

            auto new_assignments_map = assignments_map;

            for (auto branch_value = branch_domain.values.find_first() ;
                    branch_value != bitset::npos ;
                    branch_value = branch_domain.values.find_next(branch_value)) {
                auto new_assignments = assignments;
                new_assignments.emplace_back(branch_domain.v, branch_value);

                new_assignments_map[branch_domain.v] = branch_value;

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
                    // save spent clauses position
                    auto spent_clauses_restore = learned_clauses.spent_clauses.begin();

                    if (learned_clauses.propagate_assignment({ branch_domain.v, branch_value }, new_assignments_map, new_domains)) {
                        if (solve(new_domains, new_assignments, new_assignments_map))
                            return true;
                    }

                    // restore spent clauses position
                    for (auto c = learned_clauses.spent_clauses.begin() ; c != spent_clauses_restore ; ) {
                        Nogood * nogood = *c;
                        nogood->spent_list_position = learned_clauses.spent_clauses.end();
                        auto & first_list = learned_clauses.watches[nogood->assignments.at(0)];
                        nogood->first_list_position = first_list.insert(first_list.end(), nogood);
                        auto & second_list = learned_clauses.watches[nogood->assignments.at(1)];
                        nogood->second_list_position = second_list.insert(second_list.end(), nogood);
                        learned_clauses.spent_clauses.erase(c++);
                    }
                }
            }

            return false;
        }

        auto run()
        {
            vector<unsigned> assignments_map(initial_domains.size(), unassigned);
            solve(initial_domains, {}, assignments_map);

            for (auto & d : fail_depths)
                result.stats["D" + to_string(d.first)] = to_string(d.second);

            map<unsigned, unsigned> learned_clause_sizes;
            for (auto & d : learned_clauses.nogood_store)
                learned_clause_sizes[d.assignments.size()]++;

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

