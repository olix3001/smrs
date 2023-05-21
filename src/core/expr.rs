use std::hash::Hash;

use num::BigRational;

use crate::owned_vec;

/// Representation of basic mathematical expressions.
/// 
/// Some expressions are not available because they can be represented by other expressions.
/// For example, `x - y` can be represented by `x + (-y)`. And `x / y` can be represented by `x * (y ^ -1)`.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Expr {
    /// A basic number. Can be either an integer or a floating point number.
    Number(BigRational),
    /// A variable. Can be any string of characters.
    Variable(String),
    /// A sum of two or more expressions.
    Sum(Vec<Expr>),
    /// A product of two or more expressions.
    Product(Vec<Expr>),
    /// A power of one expression to another.
    Power(Box<Expr>, Box<Expr>),
    /// A negation of an expression. This is equivalent to multiplying the expression by -1.
    Negation(Box<Expr>),
    /// Basically a parenthesis. This is used to group expressions together and to change the precedence of expressions.
    Group(Box<Expr>)
}

/// Representation of the associativity of an operator.
#[derive(Debug, Clone, Hash, PartialEq, Eq)]
pub enum Associativity {
    /// The operator is left-associative.
    /// This means that `a ∘ b ∘ c` is equivalent to `(a ∘ b) ∘ c`.
    LeftAssociative,
    /// The operator is right-associative.
    /// This means that `a ∘ b ∘ c` is equivalent to `a ∘ (b ∘ c)`.
    RightAssociative,
    /// The operator is commutative.
    /// This means that `a ∘ b ∘ c` is equivalent to both `(a ∘ b) ∘ c` and `a ∘ (b ∘ c)`.
    Commutative
}

impl Expr {
    /// Prints the expression in a human-readable format. This is used mainly for debugging as it does not print the expression in a nice way.
    /// For example, `2x + 3y*z^(-1)` becomes `2*x + 3*y*z^(-1)`. 
    pub fn to_plain_string(&self) -> String {
        match self {
            Expr::Number(n) => n.to_string(),
            Expr::Variable(v) => v.to_string(),
            Expr::Sum(v) => v.iter().map(|e| e.to_plain_string()).collect::<Vec<_>>().join(" + "),
            Expr::Product(v) => v.iter().map(|e| e.to_plain_string()).collect::<Vec<_>>().join("*"),
            Expr::Power(b, e) => format!("{}^({})", b.to_plain_string(), e.to_plain_string()),
            Expr::Negation(e) => format!("-({})", e.to_plain_string()),
            Expr::Group(e) => format!("({})", e.to_plain_string())
        }
    }

    /// Returns the precedence of the expression.
    pub fn get_precedence(&self) -> isize {
        match self {
            Expr::Number(_) => 0,
            Expr::Variable(_) => 0,
            Expr::Sum(_) => 1,
            Expr::Product(_) => 2,
            Expr::Power(_, _) => 3,
            Expr::Negation(_) => 4,
            Expr::Group(_) => 5
        }
    }

    /// Returns the associativity of the expression. Expressions that are not operators are commutative.
    pub fn get_associativity(&self) -> Associativity {
        match self {
            Expr::Number(_) => Associativity::Commutative,
            Expr::Variable(_) => Associativity::Commutative,
            Expr::Sum(_) => Associativity::Commutative,
            Expr::Product(_) => Associativity::Commutative,
            Expr::Power(_, _) => Associativity::RightAssociative,
            Expr::Negation(_) => Associativity::Commutative,
            Expr::Group(_) => Associativity::Commutative
        }
    }

    /// Gets all parts of the expression. For example, `x + y` becomes `[x, y]`.
    /// This is done recursively, so `x + (y + z)` becomes `[x, y, z]`.
    /// But `x + (y * z)` becomes `[x, y * z]`. This is because the product is not the same as the sum.
    pub fn parts(&self) -> Vec<&Expr> {
        match self {
            Expr::Number(_) => vec![], // Numbers have no parts.
            Expr::Variable(_) => vec![], // Variables have no parts.
            Expr::Sum(v) => {
                let mut parts = Vec::new();
                for e in v {
                    // If the element is a sum, then add the parts of the sum.
                    // Otherwise, just add the element.
                    if let Expr::Sum(_) = e {
                        parts.extend(e.parts());
                    } else {
                        parts.push(e);
                    }
                }
                parts
            }
            Expr::Product(v) => {
                let mut parts = Vec::new();
                for e in v {
                    // If the element is a product, then add the parts of the product.
                    // Otherwise, just add the element.
                    if let Expr::Product(_) = e {
                        parts.extend(e.parts());
                    } else {
                        parts.push(e);
                    }
                }
                parts
            }
            Expr::Power(b, e) => vec![b, e], // Return the base and the exponent.
            Expr::Negation(e) => vec![e], // Return the negated expression.
            Expr::Group(e) => vec![e] // Return the grouped expression.
        }
    }

    /// Flattens similar expressions. For example, `x + (y + z)` becomes `x + y + z`.
    /// This is done recursively, so `x^(x+(y+z)) - y^((x+z)+x)` becomes `x^(x+y+z) - y^(x+z+x)`.
    pub fn flatten(&self) -> Expr {
        match self {
            Expr::Sum(_) => Expr::Sum(owned_vec!(self.parts())),
            Expr::Product(_) => Expr::Product(owned_vec!(self.parts())),
            Expr::Power(b, e) => Expr::Power(Box::new(b.flatten()), Box::new(e.flatten())),
            Expr::Negation(e) => Expr::Negation(Box::new(e.flatten())),
            Expr::Group(e) => Expr::Group(Box::new(e.flatten())),
            _ => self.clone()
        }
    }

    /// Gets all variables in the expression. For example, `x + y` becomes `[x, y]`.
    pub fn variables(&self) -> Vec<&str> {
        self.parts().iter().filter_map(|e| match e {
            Expr::Variable(v) => Some(v.as_str()),
            _ => None
        }).collect()
    }

    /// Creates new expression from original expression with parts replaced.
    /// For example, `x + y` with [x, z] as new parts becomes `x + z`.
    pub fn replace_parts(&self, parts: &[Expr]) -> Expr {
        match self {
            Expr::Number(_) => self.clone(),
            Expr::Variable(_) => self.clone(),
            Expr::Sum(_) => Expr::Sum(parts.iter().map(|e| e.clone()).collect()),
            Expr::Product(_) => Expr::Product(parts.iter().map(|e| e.clone()).collect()),
            Expr::Power(b, e) => Expr::Power(Box::new(b.replace_parts(parts)), Box::new(e.replace_parts(parts))),
            Expr::Negation(_e) => Expr::Negation(Box::new(parts[0].clone())),
            Expr::Group(_e) => Expr::Group(Box::new(parts[0].clone()))
        }
    }

    /// Mutates the expression by replacing parts with new parts.
    pub fn map_parts<F>(&self, f: F) -> Expr
        where F: Fn(&Expr) -> Expr
    {
        self.replace_parts(self.parts().iter().map(|e| {
            let e = e.clone();
            f(&e)
        }).collect::<Vec<_>>().as_slice())
    }

    /// Checks whether expression is of the same type as the other expression.
    /// This checks only the type of the expression, not the value.
    /// For example, `x + y` is the same type as `x + z`, but not the same type as `x * y`.
    pub fn is_same_type(&self, other: &Expr) -> bool {
        // TODO: Think of a better way to do this.
        match (self, other) {
            (Expr::Number(_), Expr::Number(_)) => true,
            (Expr::Variable(_), Expr::Variable(_)) => true,
            (Expr::Sum(_), Expr::Sum(_)) => true,
            (Expr::Product(_), Expr::Product(_)) => true,
            (Expr::Power(_, _), Expr::Power(_, _)) => true,
            (Expr::Negation(_), Expr::Negation(_)) => true,
            (Expr::Group(_), Expr::Group(_)) => true,
            _ => false
        }
    }


    /// Sorts an expression, for example, `y + x` becomes `x + y`.
    /// The sorting is done by comparing variables alphabetically, and numbers by their value.
    /// This is done recursively and flattens the expression so `y + (x + z)` becomes `x + y + z`.
    pub fn sort_variables(&self) -> Expr {
        // First, sort all subexpressions.
        let sorted_parts = self.parts().iter().map(|e| e.sort_variables()).collect::<Vec<_>>();
        let sorted_expr = self.replace_parts(&sorted_parts);

        let sorted_expr = match sorted_expr.flatten() {
            // If the element is a product, then sort the elements by variables.
            Expr::Product(mut v) => {
                // First, sort the elements by their variables.
                v.sort_by(|a, b| {
                    if let (Expr::Variable(v1), Expr::Variable(v2)) = (a, b) {
                        v2.cmp(&v1)
                    } else {
                        // If the element is not a variable, then it is a number.
                        std::cmp::Ordering::Less
                    }
                });
                // Then, sort numbers by their value.
                v.sort_by(|a, b| {
                    match (a, b) {
                        (Expr::Number(n1), Expr::Number(n2)) => n1.cmp(&n2),
                        (Expr::Number(_), _) => std::cmp::Ordering::Less, // Number is always less than variable.
                        (_, Expr::Number(_)) => std::cmp::Ordering::Greater, // Variable is always greater than number.
                        _ => std::cmp::Ordering::Equal // Otherwise, they are equal.
                    }
                });
                Expr::Product(v)
            },

            // If the element is a sum, then sort the elements by variables.
            Expr::Sum(mut v) => {
                // First, sort the elements by their variables.
                v.sort_by(|a, b| {
                    if let (Expr::Variable(v1), Expr::Variable(v2)) = (a, b) {
                        v1.cmp(&v2)
                    } else {
                        let va = a.variables();
                        let vb = b.variables();

                        for i in 0..va.len() {
                            if i >= vb.len() {
                                return std::cmp::Ordering::Less;
                            }
                            if va[i] != vb[i] {
                                return vb[i].cmp(&va[i]).reverse();
                            }
                        }

                        std::cmp::Ordering::Greater
                    }
                });
                // Then, sort numbers by their value.
                v.sort_by(|a, b| {
                    match (a, b) {
                        (Expr::Number(n1), Expr::Number(n2)) => n1.cmp(&n2),
                        (Expr::Number(_), _) => std::cmp::Ordering::Greater, // Number is always greater than variable.
                        (_, Expr::Number(_)) => std::cmp::Ordering::Less, // Variable is always less than number.
                        _ => std::cmp::Ordering::Equal // Otherwise, they are equal.
                    }
                });
                Expr::Sum(v)
            },
            _ => self.clone()
        };

        sorted_expr
    }

    /// Sorts the powers of the expression. For example, `x^2 + x^3` becomes `x^3 + x^2`.
    /// This can only sort if exponent is a number.
    pub fn sort_powers(&self) -> Expr {
        let flattened = self.flatten();
        let parts = flattened.parts();

        // First, sort all subexpressions.
        let mut parts = parts.iter().map(|e| e.sort_powers()).collect::<Vec<_>>();

        // Sort the powers.
        parts.sort_by(|a, b| {
            match (a.without_coefficients().ensure_power(), b.without_coefficients().ensure_power()) {
                (Expr::Power(b1, e1), Expr::Power(b2, e2)) => {
                    // Check whether the base is the same.
                    if b1 != b2 {
                        // Change the order so that nothing breaks later
                        return std::cmp::Ordering::Equal;
                    }
                    println!("e1: {} e2: {}", e1.to_plain_string(), e2.to_plain_string());
                    println!("a, b: {} {}", a.to_plain_string(), b.to_plain_string());
                    match (e1.as_ref(), e2.as_ref()) {
                        (Expr::Number(n1), Expr::Number(n2)) => {
                            // If the exponents are numbers, then compare them.
                            n2.cmp(&n1)
                        }
                        _ => std::cmp::Ordering::Greater
                    }
                },
                _ => std::cmp::Ordering::Greater
            }  
        });

        // Create new expression with sorted parts.
        flattened.replace_parts(&owned_vec!(parts))
    }

    /// Changes every variable to its power. For example, `x` becomes `x^1`.
    /// This is not done recursively, so `x + y` does not become `x^1 + y^1`.
    pub fn ensure_power(&self) -> Expr {
        match self {
            Expr::Variable(_) => Expr::Power(Box::new(self.clone()), Box::new(Expr::from(1))),
            _ => self.clone()
        }
    }

    /// Applies all sortings to the expression.
    pub fn sort(&self) -> Expr {
        // TODO: Implement stable sorting. Variables should be sorted alphabetically and powers should be sorted by their value.
        self.sort_variables().sort_powers()
    }

    /// Gets coefficients of the expression. For example, `2x + 3y` becomes `[2, 3]`.
    /// This works only for the first level of the expression.
    pub fn coefficients(&self) -> Vec<BigRational> {
        // Ensure we are working on a product.
        if let Expr::Product(_) = self {
            ()
        } else {
            return vec![BigRational::from_integer(num::BigInt::from(1))]; // If not, then return 1.
        }
        // Get coefficients from the expression.
        let mut coeffs = Vec::new();
        for e in self.parts() {
            match e {
                Expr::Number(n) => coeffs.push(n.clone()),
                _ => coeffs.push(BigRational::from_integer(num::BigInt::from(1)))
            }
        }

        // If there are no coefficients, then return 1.
        if coeffs.len() == 0 {
            vec![BigRational::from_integer(num::BigInt::from(1))]
        } else {
            coeffs
        }
    }

    /// Removes coefficients from the expression. For example, `2x` becomes `x`.
    /// This only removes coefficients from the first level of the expression.
    pub fn without_coefficients(&self) -> Expr {
        match self {
            Expr::Product(v) => {
                let mut parts = Vec::new();
                for e in v {
                    match e {
                        Expr::Number(_) => (),
                        _ => parts.push(e.clone())
                    }
                }
                if parts.len() == 1 {
                    parts[0].clone()
                } else {
                    Expr::Product(parts)
                }
            },
            _ => self.clone()
        }
    }
}

#[cfg(test)]
mod test {
    use super::*;

    #[test]
    fn test_expr() {
        let expr = Expr::from(1);
        assert_eq!(expr, Expr::Number(BigRational::from_integer(num::BigInt::from(1))));
    }

    #[test]
    fn test_expr_parts() {
        let expr = Expr::Sum(vec![Expr::from(1), Expr::Sum(vec![Expr::from(2), Expr::from(3)])]);
        assert_eq!(expr.parts(), vec![&Expr::from(1), &Expr::from(2), &Expr::from(3)]);
    }

    #[test]
    fn test_expr_flatten() {
        let expr = Expr::Sum(vec![Expr::from(1), Expr::Sum(vec![Expr::from(2), Expr::from(3)])]);
        assert_eq!(expr.flatten(), Expr::Sum(vec![Expr::from(1), Expr::from(2), Expr::from(3)]));
    }

    #[test]
    fn test_expr_sort_variables() {
        // First test product.
        let expr = Expr::Product(vec![Expr::from(1), Expr::from("x"), Expr::from(3)]);
        assert_eq!(expr.sort_variables(), Expr::Product(vec![Expr::from(1), Expr::from(3), Expr::from("x")]));

        // Then test sum.
        let expr = Expr::Sum(vec![Expr::from(1), Expr::from("x"), Expr::from(3)]);
        assert_eq!(expr.sort_variables(), Expr::Sum(vec![Expr::from("x"), Expr::from(1), Expr::from(3)]));

        // Test more complex expression of just sum.
        let expr = Expr::Sum(vec![Expr::from(1), Expr::from("x"), Expr::from(3), Expr::from("y"), Expr::from(2), Expr::from("z")]);
        assert_eq!(expr.sort_variables(), Expr::Sum(vec![Expr::from("x"), Expr::from("y"), Expr::from("z"), Expr::from(1), Expr::from(2), Expr::from(3)]));

        // Test expression with both sum and product.
        // This expression is 1 + 2y + 3x + 6, which should be 3x + 2y + 1 + 6.
        let expr = Expr::Sum(vec![Expr::from(1), Expr::Product(vec![Expr::from(2), Expr::from("y")]), Expr::Product(vec![Expr::from(3), Expr::from("x")]), Expr::from(6)]);
        assert_eq!(expr.sort_variables(), Expr::Sum(vec![Expr::Product(vec![Expr::from(3), Expr::from("x")]), Expr::Product(vec![Expr::from(2), Expr::from("y")]), Expr::from(1), Expr::from(6)]));
    }

    #[test]
    pub fn test_expr_sort_powers() {
        // x^2 + x^3 should become x^3 + x^2.
        let expr = Expr::Sum(vec![Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(2))), Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(3)))]);
        assert_eq!(expr.sort_powers(), Expr::Sum(vec![Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(3))), Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(2)))]));
    
        // x^2 + y^3 + x^3 should become x^3 + y^3 + x^2.
        // let expr = Expr::Sum(vec![Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(2))), Expr::Power(Box::new(Expr::from("y")), Box::new(Expr::from(3))), Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(3)))]);
        // assert_eq!(expr.sort(), Expr::Sum(vec![Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(3))), Expr::Power(Box::new(Expr::from("y")), Box::new(Expr::from(3))), Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(2)))]));

        // x^2 + y^3 + z^3 + x^4 should become x^4 + z^3 + y^3 + x^2.
        // let expr = Expr::Sum(vec![Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(2))), Expr::Power(Box::new(Expr::from("y")), Box::new(Expr::from(3))), Expr::Power(Box::new(Expr::from("z")), Box::new(Expr::from(3))), Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(4)))]);
        // assert_eq!(expr.sort(), Expr::Sum(vec![Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(4))), Expr::Power(Box::new(Expr::from("z")), Box::new(Expr::from(3))), Expr::Power(Box::new(Expr::from("y")), Box::new(Expr::from(3))), Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(2)))]));
    }
}