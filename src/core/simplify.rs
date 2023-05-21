use std::collections::HashMap;

use super::expr::{Expr, Associativity};

/// Combines like terms in an expression. This is a very simple simplification.
/// 
/// After this simplification, x + 2x + y + 1 + 6 will become 3x + y + 7.
/// This is done recursively, so x^(2 + 2) will also become x^4.
/// 
/// Simplifications done by this function:
/// 1. Combine like variables: x + x + x^2 + x^2 will become 2x^2 + 2x.
/// 2. Combine like numbers: 1 + 1 + 1 will become 3.
/// 
/// It also removes redundant terms and parentheses. This can be done separately by calling the `remove_redundant` function.
pub fn combine_like_terms(expr: &Expr) -> Expr {
    // Ensure we are working on a flat expression.
    let expr = remove_redundant(&expr).sort(); // This also flattens the expression.

    // And ensure we are working on a sum.
    let expr = match expr {
        Expr::Sum(parts) => Expr::Sum(parts),
        Expr::Number(_) | Expr::Variable(_) => return expr.clone(),
        _ => return expr.replace_parts(&expr.parts().iter().map(|e| combine_like_terms(e)).collect::<Vec<_>>())
    };

    // Preparation: Replace everything that looks like x^1 with x.
    let expr = expr.replace_parts(&expr.parts().iter().map(|e| {
        if let Expr::Power(base, power) = e {
            if let Expr::Number(power) = *power.clone() {
                if power == num::BigRational::from_integer(num::BigInt::from(1)) {
                    return *base.clone();
                }
            }
        }
    
        e.clone().clone()
    }).collect::<Vec<_>>());

    // Combine like terms in subexpressions.
    let expr = expr.replace_parts(&expr.parts().iter().map(|e| combine_like_terms(e)).collect::<Vec<_>>());

    // First step: Combine like variables.
    let mut coeff_map: HashMap<Expr, Expr> = HashMap::new();

    // Iterate over each part of the sum.
    for part in expr.parts() {
        // Extract all the coefficients from the part.
        let coeffs = part.coefficients();

        // Combine the coefficients.
        let mut main_coeff = num::BigRational::from_integer(num::BigInt::from(1));
        for coeff in coeffs {
            main_coeff *= coeff;
        }

        // If the main coefficient is zero, skip this part.
        if main_coeff == num::BigRational::from_integer(num::BigInt::from(0)) {
            continue;
        }

        // Check if this term is already in the coefficient map.
        if let Some(coeff) = coeff_map.get_mut(&part.without_coefficients()) {
            // If it is, add the main coefficient to the existing coefficient.
            if let Expr::Number(coeff) = coeff {
                *coeff += main_coeff;
            }
        } else {
            // If it is not, add it to the coefficient map.
            coeff_map.insert(part.without_coefficients(), Expr::Number(main_coeff));
        }
    }

    // Create a new sum with the combined coefficients.
    let mut new_expr = Vec::new();
    for (var, coeff) in coeff_map {
        new_expr.push(Expr::Product(vec![coeff, var]));
    }

    // Second step: Combine numbers.
    let mut num_sum = num::BigRational::from_integer(num::BigInt::from(0));

    // Iterate over each part of the sum.
    for part in expr.parts() {
        // If the part is just a number, add it to the number sum.
        if let Expr::Number(num) = part {
            num_sum += num;
            continue;
        }
    }

    // If the number sum is not zero, add it to the new sum.
    if num_sum != num::BigRational::from_integer(num::BigInt::from(0)) {
        new_expr.push(Expr::Number(num_sum));
    }

    // Return the new sum. This sum is already sorted.
    // TODO: Figure out how not to call `remove_redundant` two times.
    flatten_single(&remove_redundant(&Expr::Sum(new_expr)).sort())
}

/// Removes redundant terms and parentheses from an expression.
/// 
/// Simplifications done by this function:
/// 1. Remove redundant parentheses: (x) will become x, but 2(x+y) will not become 2x+2y.
/// 2. Remove unnecessary multiplication: 1x will become x and 0x will become 0.
pub fn remove_redundant(expr: &Expr) -> Expr {
    // Ensure we are working on a flat expression.
    let mut expr = expr.flatten();

    // Simplify subexpressions.
    expr = expr.replace_parts(&expr.parts().iter().map(|e| remove_redundant(e)).collect::<Vec<_>>());

    // Check for redundant parentheses. 
    // Parentheses are redundant if operation inside the parentheses is the same as the operation outside
    // the parentheses and the operation is commutative.
    if expr.get_associativity() == Associativity::Commutative {
        // Iterate through each part of the expression and check if it is a group.
        let mut new_expr: Vec<Expr> = Vec::new();

        // Simplify subexpressions.
        expr = expr.replace_parts(&expr.parts().iter().map(|e| remove_redundant(e)).collect::<Vec<_>>());

        for part in expr.parts() {
            if let Expr::Group(group) = part {
                // If it is a group, check if the operation inside the group is the same as the operation
                // outside the group.
                if group.is_same_type(&expr) {
                    // If it is, add the parts of the group to the new expression.
                    new_expr.extend(group.parts().iter().map(|e| e.clone().clone()).collect::<Vec<_>>());
                } else {
                    // If it is not, add the group to the new expression.
                    new_expr.push(part.clone());
                }
            } else {
                // If it is not a group, add it to the new expression.
                new_expr.push(part.clone());
            }
        }

        // Create a new expression from the new expression.
        expr = expr.replace_parts(new_expr.as_slice());
    }

    // Check for unnecessary multiplication.
    // Multiplication is unnecessary if the multiplier is 1 or 0.
    // In the case of 0, the entire expression will become 0.
    // In the case of 1, the multiplier will be removed.
    let mut new_expr: Vec<Expr> = Vec::new();

    // This works only if the expression is a product.
    if let Expr::Product(parts) = expr.clone() {
        // Iterate through each part of the expression.
        for part in parts {
            // If the part is a number, check if it is 0 or 1.
            if let Expr::Number(num) = part.clone() {
                if num == num::BigRational::from_integer(num::BigInt::from(0)) {
                    // If it is 0, return 0.
                    return Expr::Number(num::BigRational::from_integer(num::BigInt::from(0)));
                } else if num == num::BigRational::from_integer(num::BigInt::from(1)) {
                    // If it is 1, skip it.
                    continue;
                }
            }

            // If the part is not 0 or 1, add it to the new expression.
            new_expr.push(part.clone());
        }
    } else {
        // If the expression is not a product, return it.
        return expr.clone();
    }

    // If the new expression has only one part, return that part.

    // Create a new expression from the new expression. This expression is already sorted.
    flatten_single(&expr.replace_parts(new_expr.as_slice())).sort()
}

/// Flattens expressions if they contain only one part. This is done recursively.
#[allow(dead_code)]
fn flatten_single(expr: &Expr) -> Expr {
    // If expression is a group, flatten the group.
    if let Expr::Group(group) = expr {
        return Expr::Group(Box::new(flatten_single(group)))
    }

    // If the expression has only one part, return that part.
    if expr.parts().len() == 1 {
        return flatten_single(&expr.parts()[0]);
    } else if expr.parts().len() == 0 {
        return expr.clone();
    }

    // If the expression has more than one part, flatten each part.
    expr.replace_parts(&expr.parts().iter().map(|e| flatten_single(e)).collect::<Vec<_>>())
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_combine_like_terms() {
        let expr = Expr::Sum(vec![
            Expr::Power(Box::new(Expr::Variable("x".to_string())), Box::new(Expr::from(2))),
            Expr::Power(Box::new(Expr::Variable("x".to_string())), Box::new(Expr::from(2))),
            Expr::Power(Box::new(Expr::Variable("x".to_string())), Box::new(Expr::from(1))),
            Expr::from("x")
        ]);

        assert_eq!(combine_like_terms(&expr), Expr::Sum(vec![
            Expr::Product(vec![
                Expr::Number(num::BigRational::from_integer(num::BigInt::from(2))),
                Expr::Power(Box::new(Expr::Variable("x".to_string())), Box::new(Expr::from(2))),
            ]),
                Expr::Product(vec![
                Expr::Number(num::BigRational::from_integer(num::BigInt::from(2))),
                Expr::Variable("x".to_string()),
            ])
        ]));
    }

    #[test]
    fn test_combine_like_terms_group() {
        // Tests whether 2(x+y) + 3(x+y) becomes 5(x+y).
        let expr = Expr::Sum(vec![
            Expr::Product(vec![
                Expr::Number(num::BigRational::from_integer(num::BigInt::from(2))),
                Expr::Group(Box::new(
                    Expr::Sum(vec![
                        Expr::Variable("x".to_string()),
                        Expr::Variable("y".to_string())
                    ])
                ))
            ]),
            Expr::Product(vec![
                Expr::Number(num::BigRational::from_integer(num::BigInt::from(3))),
                Expr::Group(Box::new(
                    Expr::Sum(vec![
                        Expr::Variable("x".to_string()),
                        Expr::Variable("y".to_string())
                    ])
                ))
            ])
        ]);
        
        assert_eq!(combine_like_terms(&expr), Expr::Product(vec![
            Expr::Number(num::BigRational::from_integer(num::BigInt::from(5))),
            Expr::Group(Box::new(
                Expr::Sum(vec![
                    Expr::Variable("x".to_string()),
                    Expr::Variable("y".to_string())
                ])
            ))
        ]));
    }

    #[test]
    fn test_nested_combine_like_terms() {
        // Tests whether (x + 2x) + (2y + 4y) will become 9x.
        let expr = Expr::Sum(vec![
            Expr::Group(Box::new(
                Expr::Sum(vec![
                    Expr::Variable("x".to_string()),
                    Expr::Product(vec![
                        Expr::Number(num::BigRational::from_integer(num::BigInt::from(2))),
                        Expr::Variable("x".to_string())
                    ])
                ])
            )),
            Expr::Group(Box::new(
                Expr::Sum(vec![
                    Expr::Product(vec![
                        Expr::Number(num::BigRational::from_integer(num::BigInt::from(2))),
                        Expr::Variable("x".to_string())
                    ]),
                    Expr::Product(vec![
                        Expr::Number(num::BigRational::from_integer(num::BigInt::from(4))),
                        Expr::Variable("x".to_string())
                    ])
                ])
            ))
        ]);

        assert_eq!(combine_like_terms(&expr), Expr::Product(vec![
            Expr::Number(num::BigRational::from_integer(num::BigInt::from(9))),
            Expr::Variable("x".to_string())
        ]));
    }

    #[test]
    fn test_remove_redundant() {
        // Tests whether 1x + 0x will become x + 0.
        let expr = Expr::Sum(vec![
            Expr::Product(vec![
                Expr::Number(num::BigRational::from_integer(num::BigInt::from(1))),
                Expr::Variable("x".to_string())
            ]),
            Expr::Product(vec![
                Expr::Number(num::BigRational::from_integer(num::BigInt::from(0))),
                Expr::Variable("x".to_string())
            ])
        ]);

        assert_eq!(remove_redundant(&expr), Expr::Sum(vec![
            Expr::Variable("x".to_string()),
            Expr::Number(num::BigRational::from_integer(num::BigInt::from(0)))
        ]));

        // Tests whether x + (y + z) will become x + y + z.
        let expr = Expr::Sum(vec![
            Expr::Variable("x".to_string()),
            Expr::Group(Box::new(
                Expr::Sum(vec![
                    Expr::Variable("y".to_string()),
                    Expr::Variable("z".to_string())
                ])
            ))
        ]);

        assert_eq!(remove_redundant(&expr), Expr::Sum(vec![
            Expr::Variable("x".to_string()),
            Expr::Variable("y".to_string()),
            Expr::Variable("z".to_string())
        ]));

        // Tests whether (x + (y + z)) + w will become x + y + z + w.
        let expr = Expr::Sum(vec![
            Expr::Group(Box::new(
                Expr::Sum(vec![
                    Expr::Variable("x".to_string()),
                    Expr::Group(Box::new(
                        Expr::Sum(vec![
                            Expr::Variable("y".to_string()),
                            Expr::Variable("z".to_string())
                        ])
                    ))
                ])
            )),
            Expr::Variable("w".to_string())
        ]);

        assert_eq!(remove_redundant(&expr), Expr::Sum(vec![
            Expr::Variable("x".to_string()),
            Expr::Variable("y".to_string()),
            Expr::Variable("z".to_string()),
            Expr::Variable("w".to_string())
        ]));
    }
}