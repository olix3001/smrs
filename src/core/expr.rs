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
                    a.variables().join("").cmp(&b.variables().join(""))  
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
                Expr::Sum(v)
            },
            _ => self.clone()
        };

        sorted_expr
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
        assert_eq!(expr.sort_variables(), Expr::Sum(vec![Expr::from(1), Expr::from(3), Expr::from("x")]));

        // Test more complex expression of just sum.
        let expr = Expr::Sum(vec![Expr::from(1), Expr::from("x"), Expr::from(3), Expr::from("y"), Expr::from(2), Expr::from("z")]);
        assert_eq!(expr.sort_variables(), Expr::Sum(vec![Expr::from(1), Expr::from(2), Expr::from(3), Expr::from("x"), Expr::from("y"), Expr::from("z")]));

        // Test expression with both sum and product.
        // This expression is 1 + 2y + 3x + 6, which should be 1 + 6 + 3x + 2y.
        let expr = Expr::Sum(vec![Expr::from(1), Expr::Product(vec![Expr::from(2), Expr::from("y")]), Expr::Product(vec![Expr::from(3), Expr::from("x")]), Expr::from(6)]);
        assert_eq!(expr.sort_variables(), Expr::Sum(vec![Expr::from(1), Expr::from(6), Expr::Product(vec![Expr::from(3), Expr::from("x")]), Expr::Product(vec![Expr::from(2), Expr::from("y")])]));
    }
}