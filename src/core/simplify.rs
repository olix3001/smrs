use std::collections::HashMap;

use super::expr::Expr;

/// Combines like terms in an expression. This is a very simple simplification.
/// 
/// After this simplification, x + 2x + y + 1 + 6 will become 3x + y + 7.
/// This is done recursively, so x^(2 + 2) will also become x^4.
/// 
/// This function will first combine like powers, then like variables, then like numbers.
/// 1. Combine like variables: x + x + x^2 + x^2 will become 2x^2 + 2x.
/// 2. Combine like numbers: 1 + 1 + 1 will become 3.
pub fn combine_like_parts(expr: &Expr) -> Expr {
    // Ensure we are working on a flat expression.
    let expr = expr.flatten();
    // And ensure we are working on a sum.
    let expr = match expr {
        Expr::Sum(parts) => Expr::Sum(parts),
        Expr::Number(_) | Expr::Variable(_) => return expr.clone(),
        _ => return expr.replace_parts(&expr.parts().iter().map(|e| combine_like_parts(e)).collect::<Vec<_>>())
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
    let expr = expr.replace_parts(&expr.parts().iter().map(|e| combine_like_parts(e)).collect::<Vec<_>>());

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
    Expr::Sum(new_expr).sort()
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

        assert_eq!(combine_like_parts(&expr), Expr::Sum(vec![
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

        assert_eq!(combine_like_parts(&expr), Expr::Sum(vec![
            Expr::Product(vec![
                Expr::Number(num::BigRational::from_integer(num::BigInt::from(5))),
                Expr::Group(Box::new(
                    Expr::Sum(vec![
                        Expr::Variable("x".to_string()),
                        Expr::Variable("y".to_string())
                    ])
                ))
            ])
        ]));
    }

    #[test]
    fn test_nested_combine_like_terms() {
        // Tests whether (x + 2x) + (2y + 4y) will become (3x) + (6y).
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

        panic!("{:?}", combine_like_parts(&expr).to_plain_string());
    }
}