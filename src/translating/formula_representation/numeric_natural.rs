use {
    crate::{
        command_line::arguments::Dialect,
        convenience::{
            unbox::{Unbox as _, fol::sigma_0::UnboxedFormula},
            variable_selection::VariableSelection,
        },
        syntax_tree::{
            asp::mini_gringo as asp,
            fol::sigma_0::{
                self as fol, BinaryConnective, Formula, GeneralTerm, Guard, IntegerTerm,
                Quantification, Quantifier, Sort, Theory,
            },
        },
    },
    indexmap::IndexSet,
};

enum IndefiniteFunction {
    Division,
    Modulo,
    Interval,
}

fn construct_graphf_axiom(f: IndefiniteFunction, d: Dialect) -> fol::Formula {
    match (f, d) {
        (IndefiniteFunction::Division, Dialect::GringoFive) => {
            "forall I$ J$ Z$ ( divisionGraph(I$,J$,Z$) <->
                exists K$ (
                    K$ * |J$| <= |I$| < (K$+1) * |J$| and
                    ((I$ * J$ >= 0 and Z$ = K$) or (I$ * J$ < 0 and Z$ = -K$))))".parse().unwrap()
        },
        (IndefiniteFunction::Modulo, Dialect::GringoFive) => {
            "forall I$ J$ Z$ ( moduloGraph(I$,J$,Z$) <->
                exists K$ (
                    K$ * |J$| <= |I$| < (K$+1) * |J$| and
                    ((I$ * J$ >= 0 and Z$ = I$ - K$ * J$) or (I$ * J$ < 0 and Z$ = I$ + K$ * J$))))".parse().unwrap()
        },
        (IndefiniteFunction::Division, Dialect::GringoSix) => {
            "forall I$ J$ Q$ ( divisionGraph(I$,J$,Q$) <-> exists R$ (I$ = J$ * Q$ + R$ & J$ != 0 & 0 <= R$ < J$) )".parse().unwrap()
        },
        (IndefiniteFunction::Modulo, Dialect::GringoSix) => {
            "forall I$ J$ R$ ( moduloGraph(I$,J$,R$) <-> exists Q$ (I$ = J$ * Q$ + R$ & J$ != 0 & 0 <= R$ < J$) )".parse().unwrap()
        },
        (IndefiniteFunction::Interval, _) => {
            "forall I$ J$ K$ ( intervalGraph(I$,J$,K$) <-> I$ <= K$ <= J$ )".parse().unwrap()
        },
    }
}
