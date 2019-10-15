use egg::{
    define_term,
    egraph::EClass,
    expr::{Expr, Id, Language, Name},
};

use ordered_float::NotNan;

extern crate pest;
#[macro_use]
extern crate pest_derive;

use pest::Parser;
use std::collections::HashMap;

#[derive(Parser)]
#[grammar = "hop.pest"]
pub struct HOPParser;

pub fn parse_hop(_s: &str) -> Vec<(Vec<u32>, Id, Expr<Math, Id>, Vec<i64>)> {
    let s0 = "101,100;395;op;394,378;0,0,-1,-1,-1
101,100;395;op;394,378;0,0,-1,-1,-1
101,100;395;op;394,378;0,0,-1,-1,-1
101,100;395;op;394,378;0,0,-1,-1,-1
";

    let hops = HOPParser::parse(Rule::hops, &s0)
        .expect("parse failed").next().unwrap().into_inner();

    let mut hs = Vec::new();

    for h in hops {
        let mut hop = h.into_inner();
        // parse line number
        let line: Vec<_> = hop.next().unwrap().into_inner()
            .map(|pair| {
                pair.as_str().parse::<u32>().unwrap()
            }).collect();
        // parse hop id
        let hid = hop.next().unwrap()
            .as_str().parse::<u32>().unwrap();
        // parse operator
        let _op = hop.next()
            .unwrap().as_str();
        // parse arguments
        let args: smallvec::SmallVec<[_;2]> =
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
                let hops = hs.into_inner();

                let mut hopps = Vec::new();

                for h in hops {
                    let mut hop = h.into_inner();
                    // parse line number
                    let line: Vec<_> = hop.next().unwrap().into_inner()
                        .map(|pair| {
                            pair.as_str().parse::<u32>().unwrap()
                        }).collect();
                    // parse hop id
                    let hid = hop.next().unwrap()
                        .as_str().parse::<u32>().unwrap();
                    // parse operator
                    let _op = hop.next()
                        .unwrap().as_str();
                    // parse arguments
                    let args: smallvec::SmallVec<[_;2]> =
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

        Subst = "subst",
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
    pub schema: HashMap<Name, usize>,
}

// TODO
impl egg::egraph::Metadata<Math> for Meta {
    type Error = std::convert::Infallible;
    fn merge(&self, _other: &Self) -> Self {
        //assert_eq!(self.schema, other.schema, "merging expressions with different schema");
        self.clone()
    }

    fn make(expr: Expr<Math, &Self>) -> Self {
        let schema  = match expr.op {
            Math::Add => {
                assert_eq!(expr.children.len(), 2, "wrong length in add");
                let x = &expr.children.iter().nth(0).unwrap().schema;
                let y = &expr.children.iter().nth(1).unwrap().schema;
                let mut schema = x.clone();
                schema.extend(y.clone());
                //let schema: HashMap<Name, usize> = x.extend(y).collect(); //x.union(y).cloned().collect();
                schema
            },
            Math::Mul => {
                assert_eq!(expr.children.len(), 2, "wrong length in multiply");
                let x = &expr.children.iter().nth(0).unwrap().schema;
                let y = &expr.children.iter().nth(1).unwrap().schema;
                let mut schema = x.clone();
                schema.extend(y.clone());
                schema
            },
            Math::Agg => {
                assert_eq!(expr.children.len(), 2, "wrong length in aggregate");
                let dim = &expr.children.iter().nth(0).unwrap().schema;
                let body = &expr.children.iter().nth(1).unwrap().schema;
                let mut schema = body.clone();
                for k in dim.keys() {
                    schema.remove(k);
                }
                schema
            },
            Math::Dim => {
                assert_eq!(expr.children.len(), 2, "wrong length in dimension");
                let i = &expr.children.iter().nth(0).unwrap().schema;
                let n = &expr.children.iter().nth(1).unwrap().schema;
                let mut schema = HashMap::new();
                for k in i.keys() {
                    for v in n.values() {
                        schema.insert(k.clone(), *v);
                    }
                }
                schema
            },
            Math::Matrix => {
                let mut schema = HashMap::new();
                assert_ne!(expr.children.len(), 0, "matrix expression is empty");
                // skip to avoid couting var name in schema
                for d in expr.children.iter().skip(1) {
                    schema.extend(d.schema.clone());
                }
                schema
            },
            Math::Constant(n) => {
                let mut ns = HashMap::new();
                let un = n.round() as usize;
                ns.insert(Name::from(""), un);
                ns
            }
            Math::Variable(v) => {
                let mut ns = HashMap::new();
                ns.insert(v, 0);
                ns
            },
            Math::Subst => {
                assert_eq!(expr.children.len(), 3, "wrong length in subst");
                let e = &expr.children.iter().nth(0).unwrap().schema;
                let v = &expr.children.iter().nth(1).unwrap().schema;
                let r = &expr.children.iter().nth(2).unwrap().schema;

                let mut n = 0;

                let mut schema = r.clone();
                if e.keys().nth(0) == v.keys().nth(0) {
                    schema = r.clone();
                } else {
                    for k in v.keys() {
                        n = schema.remove(k).unwrap();
                    }
                    for k in e.keys() {
                        schema.insert(k.clone(), n);
                    };
                }
                schema
            }
        };
        println!("schema:{:?}", schema.clone());
        Self {
            schema
        }
    }

    fn modify(_eclass: &mut EClass<Math, Self>) {
    }
}
