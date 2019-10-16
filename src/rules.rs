use std::collections::hash_map::DefaultHasher;
use indexmap::IndexMap;
use std::ops::Index;
use std::hash::{Hash, Hasher};
use ordered_float::NotNan;

use log::*;

use crate::{Math, Meta};
use egg::{
    egraph::{EGraph, AddResult},
    parse::ParsableLanguage,
    pattern::{Rewrite, Applier, WildMap},
    expr::{QuestionMarkName, Expr, Name},
};
use smallvec::smallvec;

fn mk_rules(tuples: &[(&str, &str, &str)]) -> Vec<Rewrite<Math, Meta>> {
    tuples
        .iter()
        .map(|(name, left, right)| Math::parse_rewrite(name, left, right).unwrap())
        .collect()
}

pub fn run_rules(
    egraph: &mut egg::egraph::EGraph<Math, Meta>,
    iters: usize,
    limit: usize,
) {
    let rules = rules();

    'outer: for i in 0..iters {
        println!("\n\nIteration {}\n", i);

        let mut applied = 0;
        let mut matches = Vec::new();
        for (_rn, rw) in rules.iter() {
            for rule in rw {
                let ms = rule.search(&egraph);
                if !ms.is_empty() {
                    matches.push(ms);
                }
            }
        }

        for m in matches {
            let actually_matched = m.apply_with_limit(egraph, limit).len();
            if egraph.total_size() > limit {
                error!("Node limit exceeded. {} > {}", egraph.total_size(), limit);
                break 'outer;
            }

            applied += actually_matched;
            if actually_matched > 0 {
                println!("Applied {} {} times", m.rewrite.name, actually_matched);
            }
        }

        egraph.rebuild();
        println!(
            "Size: n={}, e={}",
            egraph.total_size(),
            egraph.number_of_classes()
        );

        //if applied == 0 {
        //    println!("Stopping early!");
        //    break;
        //}
    }
}

#[rustfmt::skip]
pub fn rules() -> IndexMap<&'static str, Vec<Rewrite<Math, Meta>>> {
    let mut m = IndexMap::new();
    let mut add = |name, rules| {
        if m.contains_key(name) {
            panic!("{} was already there", name);
        }
        m.insert(name, mk_rules(rules));
    };

    //add(
    //    "commutativity",
    //    &[
    //        ("+-commutative", "(+ ?a ?b)", "(+ ?b ?a)"),
    //        ("*-commutative", "(* ?a ?b)", "(* ?b ?a)"),
    //    ],
    //);
    add(
        "associativity",
        &[
            ("associate-+r+", "(+ ?a (+ ?b ?c))", "(+ (+ ?a ?b) ?c)"),
            ("associate-+l+", "(+ (+ ?a ?b) ?c)", "(+ ?a (+ ?b ?c))"),
            ("associate-+r-", "(+ ?a (- ?b ?c))", "(- (+ ?a ?b) ?c)"),
            ("associate-+l-", "(+ (- ?a ?b) ?c)", "(- ?a (- ?b ?c))"),
            ("associate--r+", "(- ?a (+ ?b ?c))", "(- (- ?a ?b) ?c)"),
            ("associate--l+", "(- (+ ?a ?b) ?c)", "(+ ?a (- ?b ?c))"),
            ("associate--l-", "(- (- ?a ?b) ?c)", "(- ?a (+ ?b ?c))"),
            ("associate--r-", "(- ?a (- ?b ?c))", "(+ (- ?a ?b) ?c)"),
            ("associate-*r*", "(* ?a (* ?b ?c))", "(* (* ?a ?b) ?c)"),
            ("associate-*l*", "(* (* ?a ?b) ?c)", "(* ?a (* ?b ?c))"),
            ("associate-*r/", "(* ?a (/ ?b ?c))", "(/ (* ?a ?b) ?c)"),
            ("associate-*l/", "(* (/ ?a ?b) ?c)", "(/ (* ?a ?c) ?b)"),
            ("associate-/r*", "(/ ?a (* ?b ?c))", "(/ (/ ?a ?b) ?c)"),
            ("associate-/l*", "(/ (* ?b ?c) ?a)", "(/ ?b (/ ?a ?c))"),
            ("associate-/r/", "(/ ?a (/ ?b ?c))", "(* (/ ?a ?b) ?c)"),
            ("associate-/l/", "(/ (/ ?b ?c) ?a)", "(/ ?b (* ?a ?c))"),
        ],
    );

    add(
        "substituting",
        &[
            ("subst-+",      "(subst ?e ?v (+ ?a ?b))",     "(+ (subst ?e ?v ?a) (subst ?e ?v ?b))"),
            ("subst-*",      "(subst ?e ?v (* ?a ?b))",     "(* (subst ?e ?v ?a) (subst ?e ?v ?b))"),
            ("subst-matrix", "(subst ?e ?v (b+ ?a ?i ?j))", "(b+ ?a (subst ?e ?v ?i) (subst ?e ?v ?j))"),
            ("subst-val",    "(subst ?e ?v (val ?n))",      "(val ?n)"),
        ],
    );

    add(
        "distributivity",
        &[
            ("distribute-lft-in",    "(* ?a (+ ?b ?c))",        "(+ (* ?a ?b) (* ?a ?c))"),
            ("distribute-rgt-in",    "(* ?a (+ ?b ?c))",        "(+ (* ?b ?a) (* ?c ?a))"),
            ("distribute-lft-out",   "(+ (* ?a ?b) (* ?a ?c))", "(* ?a (+ ?b ?c))"),
            ("distribute-lft-out--", "(- (* ?a ?b) (* ?a ?c))", "(* ?a (- ?b ?c))"),
            ("distribute-rgt-out",   "(+ (* ?b ?a) (* ?c ?a))", "(* ?a (+ ?b ?c))"),
            ("distribute-rgt-out--", "(- (* ?b ?a) (* ?c ?a))", "(* ?a (- ?b ?c))"),
            ("distribute-lft1-in",   "(+ (* ?b ?a) ?a)",        "(* (+ ?b 1) ?a)"),
            ("distribute-rgt1-in",   "(+ ?a (* ?c ?a))",        "(* (+ ?c 1) ?a)"),
        ],
    );

    //add(
    //    "agg-distribute",
    //    &[
    //        ("pullup-add",    "(SUM ?i (+ ?a ?b))",            "(+ (SUM ?i ?a) (SUM ?i ?b))"),
    //        ("pushdown-add",  "(+ (SUM ?i ?a) (SUM ?i ?b))",  "(SUM ?i (+ ?a ?b))",),
    //    ],
    //);

    add(
        "swap-aggregate",
        &[
            ("swap-agg", "(SUM ?i (SUM ?j ?a))", "(SUM ?j (SUM ?i ?a))"),
        ],
    );

    let sum_i_a = Rewrite::new(
        "sum_i_a",
        Math::parse_pattern("(SUM ?i ?a)").unwrap(),
        SumIA {
            i: "?i".parse().unwrap(),
            a: "?a".parse().unwrap(),
        },
    );

    let mul_a_agg = Rewrite::new(
        "pullup_mul",
        Math::parse_pattern("(SUM ?i (* ?a ?b))").unwrap(),
        MulAAgg {
            a: "?a".parse().unwrap(),
            b: "?b".parse().unwrap(),
            i: "?i".parse().unwrap(),
        }
    );

    let agg_i_mul = Rewrite::new(
        "pushdown_mul",
        Math::parse_pattern("(* ?a (SUM ?i ?b))").unwrap(),
        AggMul {
            a: "?a".parse().unwrap(),
            b: "?b".parse().unwrap(),
            i: "?i".parse().unwrap(),
        }
    );

    let a_subst = Rewrite::new(
        "agg-subst",
        Math::parse_pattern("(subst ?e ?v1 (SUM ?v2 ?body))").unwrap(),
        AggSubst {
            e: "?e".parse().unwrap(),
            v1: "?v1".parse().unwrap(),
            v2: "?v2".parse().unwrap(),
            body: "?body".parse().unwrap(),
        },
    );

    let v_subst = Rewrite::new(
        "dim_subst",
        Math::parse_pattern("(subst ?e ?v (dim ?i ?n))").unwrap(),
        VarSubst {
            e: "?e".parse().unwrap(),
            v: "?v".parse().unwrap(),
            i: "?i".parse().unwrap(),
            n: "?n".parse().unwrap(),
        }
    );

    m.insert("dyn_rules", vec![sum_i_a, mul_a_agg, agg_i_mul, a_subst, v_subst]);
    m
}

#[derive(Debug)]
struct VarSubst {
    e: QuestionMarkName,
    v: QuestionMarkName,
    i: QuestionMarkName,
    n: QuestionMarkName,
}

#[derive(Debug)]
struct AggSubst {
    e: QuestionMarkName,
    v1: QuestionMarkName,
    v2: QuestionMarkName,
    body: QuestionMarkName,
}

#[derive(Debug)]
struct AggMul {
    a: QuestionMarkName,
    b: QuestionMarkName,
    i: QuestionMarkName,
}

#[derive(Debug)]
struct MulAAgg {
    a: QuestionMarkName,
    b: QuestionMarkName,
    i: QuestionMarkName,
}

#[derive(Debug)]
struct SumIA {
    i: QuestionMarkName,
    a: QuestionMarkName,
}

impl Applier<Math, Meta> for SumIA {
    fn apply(&self, egraph: &mut EGraph<Math, Meta>, map: &WildMap) -> Vec<AddResult> {
        let i = map[&self.i][0];
        let a = map[&self.a][0];

        let i_schema = egraph.index(i).metadata.schema.clone();
        let a_schema = egraph.index(a).metadata.schema.clone();

        let mut res = Vec::new();

        for k in i_schema.keys() {
            if !a_schema.contains_key(k) {
                let i_abs = egraph.add(Expr::new(Math::Constant(NotNan::from(*i_schema.get(k).unwrap() as f64)), smallvec![]));
                let i_val = egraph.add(Expr::new(Math::Val, smallvec![i_abs.id]));
                let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, i_val.id]));
                res.push(mul);
            }
        }

        res
    }
}

impl Applier<Math, Meta> for MulAAgg {
    fn apply(&self, egraph: &mut EGraph<Math, Meta>, map: &WildMap) -> Vec<AddResult> {
        let i = map[&self.i][0];
        let a = map[&self.a][0];
        let b = map[&self.b][0];

        let i_schema = egraph.index(i).metadata.schema.clone();
        let a_schema = egraph.index(a).metadata.schema.clone();

        let mut res = Vec::new();

        for k in i_schema.keys() {
            if !a_schema.contains_key(k) {
                let agg = egraph.add(Expr::new(Math::Agg, smallvec![i, b]));
                let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, agg.id]));
                res.push(mul);
            }
        }

        res
    }
}

impl Applier<Math, Meta> for AggMul {
    fn apply(&self, egraph: &mut EGraph<Math, Meta>, map: &WildMap) -> Vec<AddResult> {
        let i = map[&self.i][0];
        let a = map[&self.a][0];
        let b = map[&self.b][0];

        let i_schema = egraph.index(i).metadata.schema.clone();
        let a_schema = egraph.index(a).metadata.schema.clone();

        let mut res = Vec::new();

        let k = i_schema.keys().nth(0).unwrap();

        if !a_schema.contains_key(k) {
            let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, b]));
            let agg = egraph.add(Expr::new(Math::Agg, smallvec![i, mul.id]));
            res.push(agg);
        } else {
            let mut s = DefaultHasher::new();
            [i, a, b].hash(&mut s);
            let fv = "yayay";//"v".to_owned() + &(s.finish() % 97564).to_string();

            let v = egraph.add(Expr::new(Math::Variable(Name::from(fv)), smallvec![]));
            let i_n = egraph.add(Expr::new(Math::Constant(NotNan::from(*i_schema.get(k).unwrap() as f64)), smallvec![]));
            let fdim = egraph.add(Expr::new(Math::Dim, smallvec![v.id, i_n.id]));

            //let iv = egraph.add(Expr::new(Math::Variable(k.clone()), smallvec![]));
            let b_subst = egraph.add(Expr::new(Math::Subst, smallvec![fdim.id, i, b]));

            let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, b_subst.id]));

            let agg = egraph.add(Expr::new(Math::Agg, smallvec![fdim.id, mul.id]));

            res.push(AddResult{
                was_there: false,
                id: agg.id,
            });
        }

        res
    }
}

impl Applier<Math, Meta> for AggSubst {
    fn apply(&self, egraph: &mut EGraph<Math, Meta>, map: &WildMap) -> Vec<AddResult> {
        let v1 = map[&self.v1][0];
        let v2 = map[&self.v2][0];
        let e = map[&self.e][0];
        let body = map[&self.body][0];

        let res = if v1 == v2 {
            egraph.add(Expr::new(Math::Agg, smallvec![v2, body]))
        } else {
            let sub_body = egraph.add(Expr::new(Math::Subst, smallvec![e, v1, body]));
            egraph.add(Expr::new(Math::Agg, smallvec![v2, sub_body.id]))
        };

        vec![res]
    }
}


impl Applier<Math, Meta> for VarSubst {
    fn apply(&self, egraph: &mut EGraph<Math, Meta>, map: &WildMap) -> Vec<AddResult> {
        let v = map[&self.v][0];
        let e = map[&self.e][0];
        let i = map[&self.i][0];
        let n = map[&self.n][0];

        let v_s = egraph.index(v).metadata.schema.keys().nth(0).unwrap();
        let i_schema = &egraph.index(i).metadata.schema;

        let res = if i_schema.contains_key(v_s) {
            egraph.add(Expr::new(Math::Dim, smallvec![e, n]))
        } else {
            egraph.add(Expr::new(Math::Dim, smallvec![i, n]))
        };

        vec![res]
    }
}
