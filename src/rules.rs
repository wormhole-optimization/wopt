use indexmap::IndexMap;
use std::ops::Index;
use ordered_float::NotNan;

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

#[rustfmt::skip]
pub fn rules() -> IndexMap<&'static str, Vec<Rewrite<Math, Meta>>> {
    let mut m = IndexMap::new();
    let mut add = |name, rules| {
        if m.contains_key(name) {
            panic!("{} was already there", name);
        }
        m.insert(name, mk_rules(rules));
    };

    add(
        "commutativity",
        &[
            ("+-commutative", "(+ ?a ?b)", "(+ ?b ?a)"),
            ("*-commutative", "(* ?a ?b)", "(* ?b ?a)"),
        ],
    );
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

    add(
        "agg-distribute",
        &[
            ("pullup-add",    "(SUM ?i (+ ?a ?b))",            "(+ (SUM ?i ?a) (SUM ?i ?b))"),
            ("pushdown-add",  "(+ (SUM ?i ?a) (SUM ?i ?b))",  "(SUM ?i (+ ?a ?b))",),
        ],
    );

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

    //let subst = Rewrite::new(
    //    "var_subst",
    //    Math::parse_pattern("(subst ?e ?v ?r)").unwrap(),
    //    VarSubst {
    //        e: "?e".parse().unwrap(),
    //        v: "?v".parse().unwrap(),
    //        r: "?r".parse().unwrap(),
    //    }
    //);

    m.insert("dyn_rules", vec![sum_i_a, mul_a_agg, agg_i_mul]);
    m
}

#[derive(Debug)]
struct VarSubst {
    e: QuestionMarkName,
    v: QuestionMarkName,
    r: QuestionMarkName,
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
                let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, i_abs.id]));
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

        let mut res = Vec::new();

        let i_s = i_schema.keys().nth(0).unwrap();

        let fv = "sooofresh";

        let iv = egraph.add(Expr::new(Math::Variable(i_s.clone()), smallvec![]));
        let i_n = egraph.add(Expr::new(Math::Constant(NotNan::from(*i_schema.get(i_s).unwrap() as f64)), smallvec![]));

        let v = egraph.add(Expr::new(Math::Variable(Name::from(fv)), smallvec![]));

        let fdim = egraph.add(Expr::new(Math::Dim, smallvec![v.id, i_n.id]));

        let b_subst = egraph.add(Expr::new(Math::Subst, smallvec![v.id, iv.id, b]));
        let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, b_subst.id]));
        let agg = egraph.add(Expr::new(Math::Agg, smallvec![fdim.id, mul.id]));

        res.push(agg);

        res
    }
}

//impl Applier<Math, Meta> for VarSubst {
//    fn apply(&self, egraph: &mut EGraph<Math, Meta>, map: &WildMap) -> Vec<AddResult> {
//        let e = map[&self.e][0];
//        let v = map[&self.v][0];
//        let r = map[&self.r][0];
//
//        let i_schema = egraph.index(i).metadata.schema.clone();
//        let a_schema = egraph.index(a).metadata.schema.clone();
//
//        let mut res = Vec::new();
//
//        for k in i_schema.keys() {
//            if !a_schema.contains_key(k) {
//                let agg = egraph.add(Expr::new(Math::Agg, smallvec![i, b]));
//                let mul = egraph.add(Expr::new(Math::Mul, smallvec![a, agg.id]));
//                res.push(mul);
//            }
//        }
//
//        res
//    }
//}
