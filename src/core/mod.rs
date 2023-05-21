use self::expr::Expr;

pub mod expr;

// Utilities for easier use of the library.
impl From<i32> for Expr {
    fn from(i: i32) -> Self {
        Expr::Number(num::BigRational::from_integer(num::BigInt::from(i)))
    }
}

impl From<i64> for Expr {
    fn from(i: i64) -> Self {
        Expr::Number(num::BigRational::from_integer(num::BigInt::from(i)))
    }
}

impl From<f32> for Expr {
    fn from(f: f32) -> Self {
        Expr::Number(num::BigRational::from_float(f).unwrap())
    }
}

impl From<f64> for Expr {
    fn from(f: f64) -> Self {
        Expr::Number(num::BigRational::from_float(f).unwrap())
    }
}

impl From<&str> for Expr {
    fn from(s: &str) -> Self {
        Expr::Variable(s.to_string())
    }
}

/// Converts vector of references `Vec<&T>` to vector of owned values `Vec<T>`.
/// This is done by cloning each element in the vector.
#[macro_export]
macro_rules! owned_vec {
    ($vec:expr) => {
        $vec.into_iter().map(|e| e.clone()).collect::<Vec<_>>() 
    };
}