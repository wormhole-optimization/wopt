use egg::{
    define_term,
    egraph::EClass,
    expr::{Expr, Id, Language, Name, RecExpr},
};

use ordered_float::NotNan;

extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::Parser;
use std::collections::HashSet;
use log::*;

#[derive(Parser)]
#[grammar = "hop.pest"]
pub struct HOPParser;

pub fn parse_hop(s: &str) -> Vec<(Vec<u32>, Id, Expr<Math, Id>, Vec<i64>)> {
    let s0 = "101,100;395;op;394,378;0,0,-1,-1,-1
101,100;395;op;394,378;0,0,-1,-1,-1
101,100;395;op;394,378;0,0,-1,-1,-1
101,100;395;op;394,378;0,0,-1,-1,-1
";

    let mut hops = HOPParser::parse(Rule::hops, &s0)
        .expect("parse failed").next().unwrap().into_inner();

    let mut hs = Vec::new();

    for h in hops {
        let mut hop = h.into_inner();
        // parse line number
        let mut line: Vec<_> = hop.next().unwrap().into_inner()
            .map(|pair| {
                pair.as_str().parse::<u32>().unwrap()
            }).collect();
        // parse hop id
        let hid = hop.next().unwrap()
            .as_str().parse::<u32>().unwrap();
        // parse operator
        let op = hop.next()
            .unwrap().as_str();
        // parse arguments
        let mut args: smallvec::SmallVec<[_;2]> =
            hop.next().unwrap().into_inner()
            .map(|pair| {
                pair.as_str().parse::<u32>().unwrap()
            }).collect();
        // parse metadata
        let meta: Vec<i64> = hop.next().unwrap().into_inner()
            .map(|pair| {
                pair.as_str().parse::<i64>().unwrap()
            }).collect();

        hs.push((line, hid, Expr::new(Math::Add, args), meta));
    }
    hs
}

pub fn parse_hop_file(s: &str) {
    let file = std::fs::read_to_string(s).expect("cannot read file");

    let fc = HOPParser::parse(Rule::file, &file)
        .expect("parse failed")
        .next().unwrap();

    for hs in fc.into_inner() {
        match hs.as_rule() {
            Rule::hops => {
                let mut hops = hs.into_inner();

                let mut hopps = Vec::new();

                for h in hops {
                    let mut hop = h.into_inner();
                    // parse line number
                    let mut line: Vec<_> = hop.next().unwrap().into_inner()
                        .map(|pair| {
                            pair.as_str().parse::<u32>().unwrap()
                        }).collect();
                    // parse hop id
                    let hid = hop.next().unwrap()
                        .as_str().parse::<u32>().unwrap();
                    // parse operator
                    let op = hop.next()
                        .unwrap().as_str();
                    // parse arguments
                    let mut args: smallvec::SmallVec<[_;2]> =
                        match hop.peek().unwrap().as_rule() {
                            Rule::args => {
                                hop.next().unwrap().into_inner()
                                    .map(|pair| {
                                        pair.as_str().parse::<u32>().unwrap()
                                    }).collect()
                            },
                            _ => {
                                smallvec::smallvec![]
                            }
                        };
                    // parse metadata
                    let meta: Vec<i64> = hop.next().unwrap().into_inner()
                        .map(|pair| {
                            pair.as_str().parse::<i64>().unwrap()
                        }).collect();

                    hopps.push((line, hid, Expr::new(Math::Add, args), meta));
                }
                println!("{:?}", hopps);
            }
            Rule::EOI => (),
            _ => unreachable!(),
        }
    }
}

pub type MathEGraph<M = Meta> = egg::egraph::EGraph<Math, M>;

mod rules;
pub use rules::rules;

type Constant = NotNan<f64>;

define_term! {
    #[derive(Debug, PartialEq, Eq, Hash, Clone)]
    pub enum Math {
        Add = "+",
        Mul = "*",
        Agg = "SUM",

        Dim = "dim",
        Matrix = "b+",
        Constant(Constant),
        Variable(Name),
    }
}

impl Language for Math {
    fn cost(&self, children: &[u64]) -> u64 {
        let cost = 1;
        cost + children.iter().sum::<u64>()
    }
}

#[derive(Debug, Clone)]
pub struct Meta {
    pub schema: HashSet<Name>,
}

fn eval(op: Math, args: &[Constant]) -> Option<Constant> {
    None
}

// TODO
impl egg::egraph::Metadata<Math> for Meta {
    type Error = std::convert::Infallible;
    fn merge(&self, other: &Self) -> Self {
        assert_eq!(self.schema, other.schema, "merging expressions with different schema");
        self.clone()
    }

    fn make(expr: Expr<Math, &Self>) -> Self {
        println!("ahhhhh");
        let schema  = match expr.op {
            Math::Add => {
                assert_eq!(expr.children.len(), 2, "wrong length in add");
                let x = &expr.children.iter().nth(0).unwrap().schema;
                let y = &expr.children.iter().nth(1).unwrap().schema;
                let schema: HashSet<Name> = x.union(y).cloned().collect();
                schema
            },
            Math::Mul => {
                assert_eq!(expr.children.len(), 2, "wrong length in multiply");
                let x = &expr.children.iter().nth(0).unwrap().schema;
                let y = &expr.children.iter().nth(1).unwrap().schema;
                let schema: HashSet<Name> = x.union(y).cloned().collect();
                schema
            },
            Math::Agg => {
                assert_eq!(expr.children.len(), 2, "wrong length in aggregate");
                let dim = &expr.children.iter().nth(0).unwrap().schema;
                let body = &expr.children.iter().nth(1).unwrap().schema;
                let schema: HashSet<Name> = body.difference(&dim).cloned().collect();
                schema
            },
            Math::Dim => {
                assert_eq!(expr.children.len(), 2, "wrong length in dimension");
                expr.children.iter().nth(0).unwrap().schema.clone()
            },
            Math::Matrix => {
                let mut schema = HashSet::new();
                assert_ne!(expr.children.len(), 0, "matrix expression is empty");
                // skip to avoid couting var name in schema
                for d in expr.children.iter().skip(1) {
                    schema.extend(d.schema.iter().cloned());
                }
                schema
            },
            Math::Constant(_) => HashSet::default(),
            Math::Variable(v) => {
                let mut ns = HashSet::new();
                ns.insert(v);
                ns
            },
        };
        println!("schema:{:?}", schema.clone());
        Self {
            schema
        }
    }

    fn modify(eclass: &mut EClass<Math, Self>) {
    }
}
