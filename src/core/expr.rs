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
    Negation(Box<Expr>)
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
            Expr::Negation(e) => format!("-({})", e.to_plain_string())
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
        }
    }

    /// Gets all parts of the expression. For example, `x + y` becomes `[x, y]`.
    /// This is done recursively, so `x + (y + z)` becomes `[x, y, z]`.
    /// But `x + (y * z)` becomes `[x, y * z]`. This is because the product is not the same as the sum.
    pub fn parts(&self) -> Vec<&Expr> {
        match self {
            Expr::Number(_) => vec![self], // Just return the number.
            Expr::Variable(_) => vec![self], // Just return the variable.
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
            Expr::Negation(e) => e.parts() // Return the negated expression.
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
    pub fn replace_parts(&self, parts: &[&Expr]) -> Expr {
        match self {
            Expr::Number(_) => self.clone(),
            Expr::Variable(_) => self.clone(),
            Expr::Sum(_) => Expr::Sum(parts.iter().map(|e| e.clone().clone()).collect()),
            Expr::Product(_) => Expr::Product(parts.iter().map(|e| e.clone().clone()).collect()),
            Expr::Power(b, e) => Expr::Power(Box::new(b.replace_parts(parts)), Box::new(e.replace_parts(parts))),
            Expr::Negation(e) => Expr::Negation(Box::new(e.replace_parts(parts)))
        }
    }

    /// Sorts an expression, for example, `y + x` becomes `x + y`.
    /// The sorting is done by comparing variables alphabetically, and numbers by their value.
    /// This is done recursively and flattens the expression so `y + (x + z)` becomes `x + y + z`.
    pub fn sort_variables(&self) -> Expr {
        let sorted_expr = match self.flatten() {
            // If the element is a product, then sort the elements by variables.
            Expr::Product(mut v) => {
                // First, sort the elements by their variables.
                v.sort_by(|a, b| {
                    a.variables().join("").cmp(&b.variables().join(""))  
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
                Expr::Product(v)
            },

            // If the element is a sum, then sort the elements by variables.
            Expr::Sum(mut v) => {
                // First, sort the elements by their variables.
                v.sort_by(|a, b| {
                    a.variables().join("").cmp(&b.variables().join(""))  
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
        let mut parts = flattened.parts();

        // Sort the powers.
        parts.sort_by(|a, b| {
            match (a, b) {
                (Expr::Power(b1, e1), Expr::Power(b2, e2)) => {
                    // Check whether the base is the same.
                    if b1 != b2 {
                        return std::cmp::Ordering::Equal;
                    }
                    match (e1.as_ref(), e2.as_ref()) {
                        (Expr::Number(n1), Expr::Number(n2)) => n1.cmp(&n2).reverse(),
                        _ => std::cmp::Ordering::Equal
                    }
                },
                _ => std::cmp::Ordering::Equal
            }  
        });

        // Create new expression with sorted parts.
        flattened.replace_parts(&parts)
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
        assert_eq!(expr.sort_variables(), Expr::Product(vec![Expr::from("x"), Expr::from(1), Expr::from(3)]));

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
    
        // x^2 + y^3 + x^3 should become x^3 + x^2 + y^3.
        let expr = Expr::Sum(vec![Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(2))), Expr::Power(Box::new(Expr::from("y")), Box::new(Expr::from(3))), Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(3)))]);
        assert_eq!(expr.sort_variables().sort_powers(), Expr::Sum(vec![Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(3))), Expr::Power(Box::new(Expr::from("x")), Box::new(Expr::from(2))), Expr::Power(Box::new(Expr::from("y")), Box::new(Expr::from(3)))]));
    }
}