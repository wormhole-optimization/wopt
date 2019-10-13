use indexmap::IndexMap;

use crate::Math;
use egg::{egraph::Metadata, parse::ParsableLanguage, pattern::Rewrite};

fn mk_rules<M: Metadata<Math>>(tuples: &[(&str, &str, &str)]) -> Vec<Rewrite<Math, M>> {
    tuples
        .iter()
        .map(|(name, left, right)| Math::parse_rewrite(name, left, right).unwrap())
        .collect()
}

#[rustfmt::skip]
pub fn rules<M: Metadata<Math>>() -> IndexMap<&'static str, Vec<Rewrite<Math, M>>> {
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

    m
}
