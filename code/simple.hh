/* vim: set sw=4 sts=4 et foldmethod=syntax : */

#ifndef CODE_GUARD_SIMPLE_HH
#define CODE_GUARD_SIMPLE_HH 1

#include "graph.hh"
#include "params.hh"
#include "result.hh"

auto simple_subgraph_isomorphism(const std::pair<Graph, Graph> & graphs, const Params & params) -> Result;

#endif
