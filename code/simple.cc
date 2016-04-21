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
    };

    struct VariablesStack
    {
        std::vector<Variables> variables;

        VariablesStack(unsigned depth, unsigned width) :
            variables(depth + 1, Variables{ width })
            {
            }
    };

    auto initialise_variables(const std::pair<Graph, Graph> & graphs, const Params &, Variables & variables)
    {
        for (unsigned p = 0 ; p < graphs.first.size() ; ++p) {
            variables.domains.emplace(p, std::set<unsigned>());
            for (unsigned t = 0 ; t < graphs.second.size() ; ++t) {
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

    auto solve(const std::pair<Graph, Graph> & graphs, const Params & params, Result & result,
            VariablesStack & variables_stack, unsigned stack_level) -> bool
    {
        if (*params.abort)
            return false;

        ++result.nodes;

        auto & variables = variables_stack.variables.at(stack_level);

        auto branch_variable = smallest_domain(variables);
        if (branch_variable == variables.domains.end())
            return true;

        if (branch_variable->second.empty()) {
            std::cerr << "wipeout on " << branch_variable->first << " at depth " << stack_level << std::endl;
            return false;
        }

        for (auto & t : branch_variable->second) {
            result.isomorphism[branch_variable->first] = t;

            auto & next_variables = variables_stack.variables.at(stack_level + 1);
            next_variables = variables;

            next_variables.domains.erase(branch_variable->first);

            for (auto & d : next_variables.domains) {
                // propagate all-different
                d.second.erase(t);

                // propagate adjacency
                if (graphs.first.adjacent(branch_variable->first, d.first))
                    for (auto i = d.second.begin() ; i != d.second.end() ; )
                        if (graphs.second.adjacent(t, *i))
                            ++i;
                        else
                            d.second.erase(i++);
            }

            if (solve(graphs, params, result, variables_stack, stack_level + 1))
                return true;
        }

        return false;
    }
}

auto simple_subgraph_isomorphism(const std::pair<Graph, Graph> & graphs, const Params & params) -> Result
{
    Result result;

    VariablesStack variables_stack(graphs.first.size(), graphs.second.size());

    initialise_variables(graphs, params, variables_stack.variables.at(0));
    solve(graphs, params, result, variables_stack, 0);

    return result;
}

