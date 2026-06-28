use crate::syntax_tree::asp::mini_gringo::Rule;

pub fn numeric_normal_form(rule: Rule) -> Rule {
    rule
}

#[cfg(test)]
mod tests {

    use super::numeric_normal_form;

    #[test]
    fn test_numeric_normal_form() {
        for (src, target) in [
                (
                    "p(1..8).", "p(V) :- V = 1..8."
                ),
                (
                    "q(1..(X/2)) :- p(X).", "q(V1) :- p(X), V = X/2, V1 = 1..V."
                ),
        ] {
            let src = numeric_normal_form(src.parse().unwrap());
            let target = target.parse().unwrap();
            assert_eq!(src, target, "\n{src} \n!= \n{target}")
        }
    }
}
