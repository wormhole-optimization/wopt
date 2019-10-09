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

#[test]
fn hop_parse(){ 
  println!("{:?}", parse_hop_file("/Users/remywang/wormhole/wopt/tests/hops"));
}

static HOP:&str ="101;395;op;394,378;0,0,-1,-1,-1; ...";

static HOPS:&str = "(359);u(print);;[-1,-1,-1,-1,-1]; [-,0,0 -> 0MB]
(388);u(print);;[-1,-1,-1,-1,-1]; [-,0,0 -> 0MB]
(385);TRead y;;[10000,1,1000,1000,10000]; [0,0,0 -> 0MB]
(389);ua(+RC);(385);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(391);b(/);(389);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(514);b(+);(391);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(394);b(^);(385);[10000,1,1000,1000,10000]; [0,0,0 -> 0MB]
(395);ua(+RC);(394);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(399);b(^);(391);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(400);b(*);(399);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(401);b(-);(395,400);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(406);b(/);(401);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(516);u(sqrt);(406);[-1,-1,-1,-1,-1]; [0,0,0 -> 0MB]
(517);b(+);(516);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(518);b(cbind);(514,517);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(384);TRead X;;[10000,1000,1000,1000,9001506]; [0,0,18205 -> 18205MB]
(379);TRead beta_unscaled;;[1000,1,1000,1000,-1]; [0,0,18205 -> 18205MB]
(408);ba(+*);(384,379);[10000,1,1000,1000,-1]; [36409,0,0 -> 36409MB]
(409);b(-);(385,408);[10000,1,1000,1000,-1]; [0,0,0 -> 0MB]
(410);ua(+RC);(409);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(412);b(/);(410);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(520);b(+);(412);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(521);b(cbind);(518,520);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(415);b(^);(409);[10000,1,1000,1000,-1]; [0,0,0 -> 0MB]
(416);ua(+RC);(415);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(420);b(^);(412);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(421);b(*);(420);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(422);b(-);(416,421);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(466);b(/);(422);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(523);u(sqrt);(466);[-1,-1,-1,-1,-1]; [0,0,0 -> 0MB]
(524);b(+);(523);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(525);b(cbind);(521,524);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(432);b(/);(416);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(434);t(ifelse);(432);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(527);b(+);(434);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(528);b(cbind);(525,527);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(425);b(/);(416,401);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(426);b(-);(425);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(530);b(+);(426);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(531);b(cbind);(528,530);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(443);b(/);(434,406);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(444);b(-);(443);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(446);t(ifelse);(444);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(533);b(+);(446);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(534);b(cbind);(531,533);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(449);b(/);(422,401);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(450);b(-);(449);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(536);b(+);(450);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(537);b(cbind);(534,536);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(472);b(/);(466,406);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(473);b(-);(472);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(539);b(+);(473);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(540);b(cbind);(537,539);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(495);b(/);(416,395);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(496);b(-);(495);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(550);b(+);(496);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(551);b(cbind);(540,550);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(507);b(/);(395);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(508);b(/);(432,507);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(509);b(-);(508);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(511);t(ifelse);(509);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(553);b(+);(511);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(554);b(cbind);(551,553);[0,0,-1,-1,-1]; [0,0,0 -> 0MB]
(569);u(print);(554);[-1,-1,-1,-1,-1]; [0,0,0 -> 0MB]
(571);u(print);;[-1,-1,-1,-1,-1]; [-,0,0 -> 0MB]
(590);PWrite beta_out;(379);[1000,1,-1,-1,-1]; [18204,0,18205 -> 36409MB]
(604);u(print);;[-1,-1,-1,-1,-1]; [-,0,0 -> 0MB]
";

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
    //let mut id_map: HashMap<Id, Id> = HashMap::new();

    //let (id, exp) = x_id;
    //let node = exp.map_children(|child| *id_map.get(&child).unwrap());
    //let new_id = eg.add(node).id;
    //id_map.insert(id, new_id);

    //let (id, exp) = y_id;
    //let node = exp.map_children(|child| *id_map.get(&child).unwrap());
    //let new_id = eg.add(node).id;
    //id_map.insert(id, new_id);

    //let (id, exp) = plus_id;
    //let node = exp.map_children(|child| *id_map.get(&child).unwrap());
    //let new_id = eg.add(node).id;
    //id_map.insert(id, new_id);

    eg.dump_dot("wopt.dot");
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

    let (mut egraph, _root) = EGraph::<Math, ()>::from_expr(&start_expr);

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

fn run_rules<M>(egraph: &mut EGraph<Math, M>, iters: usize, limit: usize) -> Duration
where
    M: Metadata<Math>,
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
        start: "(+ x y)",
        end: "(/ x y)",
        iters: 5,
        limit: 1_000,
    }
    .check();
}

#[test]
fn simplifies() {
    CheckSimplify {
        start: r#"
          (/ 1
             (- (/ (+ 1 (sqrt five))
                   2)
                (/ (- 1 (sqrt five))
                   2)))
        "#,
        end: "(/ 1 (sqrt five))",
        iters: 6,
        limit: 75_000,
    }
    .check();
}

#[test]
fn fold_after_rewrite() {
    CheckSimplify {
        start: "
          (+ 1
             (- a
                (* (- 2 1)
                   a)))",
        end: "1",
        iters: 4,
        limit: 10_000,
    }
    .check();
}

static EXP: &str = r#"
(/
 (*
  (*
   (*
    (pow
     (/ 1 (+ 1 (exp (- 0 s))))
     c_p)
    (pow
     (- 1 (/ 1 (+ 1 (exp (- 0 s)))))
     c_n))
   (*
    (pow
     (/ 1 (+ 1 (exp (- 0 s))))
     c_p)
    (pow
     (- 1 (/ 1 (+ 1 (exp (- 0 s)))))
     c_n)))
  (*
   (pow
    (/ 1 (+ 1 (exp (- 0 s))))
    c_p)
   (pow
    (- 1 (/ 1 (+ 1 (exp (- 0 s)))))
    c_n)))
 (*
  (*
   (*
    (pow
     (/ 1 (+ 1 (exp (- 0 t))))
     c_p)
    (pow
     (- 1 (/ 1 (+ 1 (exp (- 0 t)))))
     c_n))
   (*
    (pow
     (/ 1 (+ 1 (exp (- 0 t))))
     c_p)
    (pow
     (- 1 (/ 1 (+ 1 (exp (- 0 t)))))
     c_n)))
  (*
   (pow
    (/ 1 (+ 1 (exp (- 0 t))))
    c_p)
   (pow
    (- 1 (/ 1 (+ 1 (exp (- 0 t)))))
    c_n))))
"#;

#[test]
fn do_something() {
    let _ = env_logger::builder().is_test(true).try_init();
    let start_expr = Math::parse_expr(EXP).unwrap();
    let (mut egraph, root) = EGraph::<Math, Meta>::from_expr(&start_expr);

    let herbies_result = "(*
  (*
   (*
    (/
     (pow (- 1 (/ 1 (+ (exp (- 0 s)) 1))) c_n)
     (pow (- 1 (/ 1 (+ (exp (- 0 t)) 1))) c_n))
    (/ (pow (/ 1 (+ (exp (- 0 s)) 1)) c_p) (pow (/ 1 (+ (exp (- 0 t)) 1)) c_p)))
   (*
    (/
     (pow (- 1 (/ 1 (+ (exp (- 0 s)) 1))) c_n)
     (pow (- 1 (/ 1 (+ (exp (- 0 t)) 1))) c_n))
    (/ (pow (/ 1 (+ (exp (- 0 s)) 1)) c_p) (pow (/ 1 (+ (exp (- 0 t)) 1)) c_p))))
  (*
   (/
    (pow (- 1 (/ 1 (+ (exp (- 0 s)) 1))) c_n)
    (pow (- 1 (/ 1 (+ (exp (- 0 t)) 1))) c_n))
   (/ (pow (/ 1 (+ (exp (- 0 s)) 1)) c_p) (pow (/ 1 (+ (exp (- 0 t)) 1)) c_p))))";

    let other_expr = Math::parse_expr(herbies_result).unwrap();
    println!(
        "Herbie ({}): {}",
        calculate_cost(&other_expr),
        other_expr.to_sexp()
    );

    run_rules(&mut egraph, 3, 20_000);
    let start_time = Instant::now();

    let ext = Extractor::new(&egraph);
    let best = ext.find_best(root);
    let extract_time = start_time.elapsed();

    println!(
        "Start ({}): {}",
        calculate_cost(&start_expr),
        start_expr.to_sexp()
    );
    println!("Best ({}): {}", best.cost, best.expr.to_sexp());

    println!("Extract time: {:.4}", extract_time.as_secs_f64());
}
