use egg::{
    egraph::{EGraph, Metadata},
    expr::{Expr, Id},
    extract::{calculate_cost, Extractor},
    parse::ParsableLanguage,
    pattern::Pattern,
};
use log::*;
use std::time::{Duration, Instant};
use smallvec::smallvec;

use wopt::{Math, Meta, parse_hop, parse_hop_file};

use std::collections::HashMap;

//#[test]
fn hop_parse(){
  println!("{:?}", parse_hop_file("/Users/r/wormhole/wopt/tests/hops"));
}

static HOP:&str ="101;395;op;394,378;0,0,-1,-1,-1; ...";

#[test]
fn wopt() {
    // input are DAG of operators
    // 10 var(x) []
    // 11 var(y) []
    // 12 add [10, 11]
    let x: Expr<Math, Id> = Expr::new(
        Math::Variable("x".parse().unwrap()),
        smallvec![]);
    let x_id = (10, x);

    let y: Expr<Math, Id> = Expr::new(
        Math::Variable("y".parse().unwrap()),
        smallvec![]);
    let y_id = (11, y);

    let plus: Expr<Math, Id> = Expr::new(
        Math::Add, smallvec![10, 11]);
    let plus_id = (12, plus);

    let hop = [x_id, y_id, plus_id];

    let mut eg: EGraph<Math, Meta> = EGraph::default();

    from_dag(&mut eg, &hop);
    eg.dump_dot("wopt.dot");
}

#[test]
fn schema() {
    // let _ = env_logger::builder().is_test(true).try_init();
    let start = "(+ x y)";// "(SUM (dim j 10) (* (b+ a (dim i 5) (dim j 10)) (b+ b (dim j 10) (dim k 7))))";
    let start_expr = Math::parse_expr(start).unwrap();

    let (mut egraph, _root) = EGraph::<Math, Meta>::from_expr(&start_expr);
    run_rules(&mut egraph, 4, 500);

    //let rules = wopt::rules();

    egraph.dump_dot("schema.dot");
}

#[test]
fn grammar() {
    let start = "(subst i j (+ a (+ b j)))";
    let start_expr = Math::parse_expr(start).unwrap();

    let (mut egraph, _root) = EGraph::<Math, Meta>::from_expr(&start_expr);

    //let rules = wopt::rules();

    for _ in 0..2 {
        for (_name, rs) in wopt::rules() {
            for rule in rs {
                rule.run(&mut egraph);
                egraph.rebuild();
            }
        }
    }
    egraph.dump_dot("grammar.dot");
}

fn from_dag(eg: &mut EGraph<Math, Meta>, dag: &[(Id, Expr<Math, Id>)]) {
    let mut id_map: HashMap<Id, Id> = HashMap::new();

    for (id, exp) in dag {
        let node = exp.map_children(|child| {
            *id_map.get(&child).expect("DAG parent inserted before its child")
        });
        id_map.insert(*id, eg.add(node).id);
    }
}

#[test]
fn associate_adds() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start = "(+ 1 (+ 2 (+ 3 (+ 4 (+ 5 (+ 6 7))))))";
    let start_expr = Math::parse_expr(start).unwrap();

    let (mut egraph, _root) = EGraph::<Math, Meta>::from_expr(&start_expr);

    let rules = {
        let all = wopt::rules();
        let mut r = Vec::new();
        r.extend(all["associativity"].clone());
        r.extend(all["commutativity"].clone());
        r
    };

    for _ in 0..4 {
        for rule in &rules {
            rule.run(&mut egraph);
            egraph.rebuild();
        }
    }

    // there are exactly 127 non-empty subsets of 7 things
    assert_eq!(egraph.number_of_classes(), 127);

    egraph.dump_dot("associate.dot");
}

fn run_rules(egraph: &mut EGraph<Math, Meta>, iters: usize, limit: usize) -> Duration
{
    let rules = wopt::rules();
    let start_time = Instant::now();

    for i in 0..iters {
        println!("\n\nIteration {}\n", i);

        let search_time = Instant::now();

        let mut applied = 0;
        let mut total_matches = 0;
        let mut last_total_matches = 0;
        let mut matches = Vec::new();
        for (_name, list) in rules.iter() {
            for rule in list {
                let ms = rule.search(&egraph);
                if !ms.is_empty() {
                    matches.push(ms);
                }
                // rule.run(&mut egraph);
                // egraph.rebuild();
            }
        }

        println!("Search time: {:.4}", search_time.elapsed().as_secs_f64());

        let match_time = Instant::now();

        for m in matches {
            let actually_matched = m.apply_with_limit(egraph, limit);
            if egraph.total_size() > limit {
                panic!("Node limit exceeded. {} > {}", egraph.total_size(), limit);
            }

            applied += actually_matched.len();
            total_matches += m.len();

            // log the growth of the egraph
            if total_matches - last_total_matches > 1000 {
                last_total_matches = total_matches;
                let elapsed = match_time.elapsed();
                debug!(
                    "nodes: {}, eclasses: {}, actual: {}, total: {}, us per match: {}",
                    egraph.total_size(),
                    egraph.number_of_classes(),
                    applied,
                    total_matches,
                    elapsed.as_micros() / total_matches as u128
                );
            }
        }

        println!("Match time: {:.4}", match_time.elapsed().as_secs_f64());

        let rebuild_time = Instant::now();
        egraph.rebuild();
        // egraph.prune();
        println!("Rebuild time: {:.4}", rebuild_time.elapsed().as_secs_f64());
    }

    println!("Final size {}", egraph.total_size());

    let rules_time = start_time.elapsed();
    println!("Rules time: {:.4}", rules_time.as_secs_f64());

    rules_time
}

#[must_use]
struct CheckSimplify {
    start: &'static str,
    end: &'static str,
    iters: usize,
    limit: usize,
}

impl CheckSimplify {
    fn check(self) {
        let _ = env_logger::builder().is_test(true).try_init();
        let start_expr = Math::parse_expr(self.start).unwrap();
        let end_expr = Math::parse_expr(self.end).unwrap();

        let (mut egraph, root) = EGraph::<Math, Meta>::from_expr(&start_expr);
        run_rules(&mut egraph, self.iters, self.limit);

        let ext = Extractor::new(&egraph);
        let best = ext.find_best(root);
        println!("Best ({}): {}", best.cost, best.expr.to_sexp());

        if best.expr != end_expr {
            println!("start: {}", start_expr.to_sexp());
            println!("start: {:?}", start_expr);
            panic!("Could not simplify {} to {}", self.start, self.end);
        }

        // make sure that pattern search also works
        let pattern = Pattern::from_expr(&end_expr);
        let matches = pattern.search_eclass(&egraph, root).unwrap();
        assert!(!matches.mappings.is_empty());
    }
}

#[test]
#[should_panic(expected = "Could not simplify")]
fn does_not_simplify() {
    CheckSimplify {
        start: "(SUM (dim j 10) (b+ a (dim i 5) (dim k 10)))",//;"(+ x y)",
        end: "(/ x y)",
        iters: 5,
        limit: 1_000,
    }
    .check();
}
