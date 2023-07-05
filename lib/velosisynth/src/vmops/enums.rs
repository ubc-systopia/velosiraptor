use std::collections::{HashMap, HashSet};
use std::fmt::Display;
use std::rc::Rc;

use itertools::Itertools;
use petgraph::stable_graph::{EdgeIndex, NodeIndex, StableUnGraph};
use petgraph::visit::IntoNodeReferences;
use petgraph::visit::{EdgeRef, IntoEdgeReferences};
use petgraph::Undirected;

use crate::model::{
    expr::{self, model_slice_accessor_read_fn, p2p},
    types,
};
use crate::z3::Z3Result;
use crate::{Z3Query, Z3TaskPriority, Z3WorkerPool};
use smt2::{Smt2Context, Smt2Option, Term};
use velosiast::{ast::VelosiAstExpr, VelosiAstUnitEnum};

#[derive(Debug, Clone)]
struct Node(Rc<String>, Vec<Rc<VelosiAstExpr>>);

impl Display for Node {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(
            f,
            "Node({}, {:?})",
            self.0,
            self.1.iter().map(|e| format!("{e}")).collect::<Vec<_>>()
        )
    }
}

#[derive(Debug, Clone)]
struct Edge(Rc<VelosiAstExpr>, Rc<VelosiAstExpr>, Vec<Rc<String>>);

impl Display for Edge {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        write!(f, "Edge({}, {})", self.0, self.1)
    }
}

pub fn distinguish(
    z3: &mut Z3WorkerPool,
    models: &HashMap<Rc<String>, Smt2Context>,
    e: &mut VelosiAstUnitEnum,
) {
    // create model
    let mut smt = Smt2Context::new();
    // set the options
    smt.set_option(Smt2Option::ProduceUnsatCores(true));

    for variant in e.get_unit_names().iter() {
        smt.merge(models[*variant].clone());
    }
    z3.reset_with_context(Z3Query::from(smt));

    // create the graph
    let mut graph = StableUnGraph::<Node, Edge>::default();

    for (variant, differentiators) in e.get_unit_differentiators().iter() {
        graph.add_node(Node(variant.clone(), differentiators.to_vec()));
    }

    let mut edges = Vec::new();
    graph
        .node_references()
        .tuple_combinations()
        .for_each(|((idx1, node1), (idx2, node2))| {
            if idx1 != idx2 {
                for e1 in &node1.1 {
                    for e2 in &node2.1 {
                        let mut refs1 = HashSet::new();
                        let mut refs2 = HashSet::new();

                        e1.get_state_references(&mut refs1);
                        e2.get_state_references(&mut refs2);

                        let refs = refs1.intersection(&refs2).cloned().collect::<Vec<_>>();
                        if !refs.is_empty() {
                            edges.push((idx1, idx2, Edge(e1.clone(), e2.clone(), refs)));
                        }
                    }
                }
            }
        });

    for (idx1, idx2, e) in edges {
        graph.add_edge(idx1, idx2, e);
    }

    let mut edges_to_remove = Vec::new();
    for edge in graph.edge_references() {
        let (result, to_remove) = submit_edge_query(edge, &graph, z3);

        // we got a result, check if it's sat
        if !result.unwrap().result().starts_with("sat") {
            edges_to_remove.push(to_remove);
        }
    }

    for (id, source_id, target_id) in edges_to_remove {
        let edge = graph.remove_edge(id).expect("edge to be found");

        let mut source_refs = HashSet::new();
        graph.edges(source_id).for_each(|e| {
            e.weight().0.get_state_references(&mut source_refs);
            e.weight().1.get_state_references(&mut source_refs);
        });
        if !edge.2.iter().any(|sref| source_refs.contains(sref)) {
            graph[source_id].1.retain(|e| e != &edge.0 && e != &edge.1);
        }

        let mut target_refs = HashSet::new();
        graph.edges(target_id).for_each(|e| {
            e.weight().0.get_state_references(&mut target_refs);
            e.weight().1.get_state_references(&mut target_refs);
        });
        if !edge.2.iter().any(|sref| target_refs.contains(sref)) {
            graph[target_id].1.retain(|e| e != &edge.0 && e != &edge.1);
        }
    }

    if fully_connected(&graph) {
        println!("distinguishable");
        let indices = graph.node_indices().collect::<Vec<_>>();
        for idx in indices {
            let node = graph.remove_node(idx).unwrap();
            e.set_unit_differentiator(&node.0, node.1)
        }
    } else {
        // TODO: emit warning
        println!("not distinguishable");
    }
}

fn submit_edge_query(
    edge: petgraph::stable_graph::EdgeReference<'_, Edge>,
    graph: &petgraph::stable_graph::StableGraph<Node, Edge, Undirected>,
    z3: &mut Z3WorkerPool,
) -> (Option<Z3Result>, (EdgeIndex, NodeIndex, NodeIndex)) {
    // check distinguishable, remove if not
    let source_id = edge.source();
    let source_node = &graph[source_id];
    let target_id = edge.target();
    let target_node = &graph[target_id];
    let id = edge.id();
    let edge = edge.weight();
    let state_refs = &edge.2;

    // create query
    let mut smt = Smt2Context::new();

    // create a precondition that all enum models must have the same value for the same named state field
    let pre = Term::fn_apply(
        "and".to_string(),
        state_refs
            .iter()
            .map(|state_ref| {
                let mut s = state_ref.split('.');
                let part = p2p(s.next().unwrap());
                let field = s.next().unwrap();
                let slice = s.next().unwrap();

                Term::fn_apply(
                    "=".to_string(),
                    [&source_node.0, &target_node.0]
                        .iter()
                        .enumerate()
                        .map(|(i, variant)| {
                            let param = format!("st!{i}");

                            model_slice_accessor_read_fn(variant, &param, part, field, slice)
                        })
                        .collect(),
                )
            })
            .collect(),
    );

    let mut vars = Vec::new();
    let mut exprs = Vec::new();
    for (i, node) in [&source_node, &target_node].iter().enumerate() {
        let (variant, preconds) = (&node.0, &node.1);
        let param = format!("st!{i}");
        vars.push(smt2::SortedVar::new(param.clone(), types::model(variant)));

        let expr = Term::fn_apply(
            "and".to_string(),
            preconds
                .iter()
                .filter(|p| {
                    let mut refs = HashSet::new();
                    p.get_state_references(&mut refs);
                    refs.iter().all(|x| state_refs.contains(x))
                })
                .map(|p| expr::expr_to_smt2(variant, p, &param))
                .collect(),
        );
        exprs.push(expr);
    }
    let expr = Term::fn_apply(
        "<=".to_string(),
        vec![
            Term::fn_apply(
                "+".to_string(),
                exprs
                    .into_iter()
                    .map(|e| {
                        Term::ifelse(e, Term::ident(1.to_string()), Term::ident(0.to_string()))
                    })
                    .collect(),
            ),
            Term::ident(1.to_string()),
        ],
    );

    let t = Term::implies(pre, expr);

    let forall = Term::forall(vars, t);

    smt.assert(forall);
    smt.check_sat();

    let mut smtctx = Smt2Context::new();
    smtctx.level(smt);

    let ticket = z3
        .submit_query(Box::new(Z3Query::from(smtctx)), Z3TaskPriority::Medium)
        .expect("failed to submit query");
    let mut result = None;
    while result.is_none() {
        result = z3.get_result(ticket);
    }
    (result, (id, source_id, target_id))
}

// TODO: sequential for now
fn fully_connected(graph: &StableUnGraph<Node, Edge>) -> bool {
    let node_ids = graph
        .node_references()
        .map(|(id, _)| id)
        .collect::<Vec<_>>();
    for (node_id, _) in graph.node_references() {
        let mut reachable = graph
            .edges(node_id)
            .map(|edge| edge.target())
            .chain([node_id])
            .collect::<Vec<_>>();

        for n_id in &node_ids {
            match reachable.iter().position(|r_id| r_id == n_id) {
                Some(idx) => reachable.remove(idx),
                None => return false,
            };
        }

        if !reachable.is_empty() {
            // TODO: emit warning
        }
    }

    true
}
