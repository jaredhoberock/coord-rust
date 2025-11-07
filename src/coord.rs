use crate::{congruent, requires, weakly_congruent};
use crate::shape::Shape;

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Coord {
    Scalar(i64),
    Tuple(Vec<Coord>),
}

impl Coord {
    pub fn shape(&self) -> Shape {
        match self {
            Coord::Scalar(_) => Shape::Scalar,
            Coord::Tuple(xs) => Shape::Tuple(xs.iter().map(|c| c.shape()).collect()),
        }
    }

    fn zero_from_shape(s: &Shape) -> Self {
        match s {
            Shape::Scalar => Coord::Scalar(0),
            Shape::Tuple(xs) => Coord::Tuple(xs.iter().map(Self::zero_from_shape).collect()),
        }
    }

    pub fn rank(&self) -> usize {
        self.shape().rank()
    }

    pub fn is_congruent_to(&self, other: &Self) -> bool {
        self.shape().is_congruent_to(&other.shape())
    }

    pub fn is_weakly_congruent_to(&self, other: &Self) -> bool {
        self.shape().is_weakly_congruent_to(&other.shape())
    }

    #[congruent(other, result)]
    pub fn sum(&self, other: &Self) -> Self {
        match (self, other) {
            (Coord::Scalar(a), Coord::Scalar(b)) => Coord::Scalar(a + b),
            (Coord::Tuple(xs), Coord::Tuple(ys)) => Coord::Tuple(
                xs.iter().zip(ys.iter()).map(|(x, y)| x.sum(y)).collect()
            ),
            _ => unreachable!("invariant broken: Coords must be congruent")
        }
    }

    #[congruent(other, result)]
    pub fn difference(&self, other: &Self) -> Self {
        match (self, other) {
            (Coord::Scalar(a), Coord::Scalar(b)) => Coord::Scalar(a - b),
            (Coord::Tuple(xs), Coord::Tuple(ys)) => Coord::Tuple(
                xs.iter().zip(ys.iter()).map(|(x, y)| x.difference(y)).collect()
            ),
            _ => unreachable!("invariant broken: Coords must be congruent")
        }
    }

    #[congruent(other)]
    pub fn inner_product(&self, other: &Self) -> i64 {
        match (self, other) {
            (Coord::Scalar(a), Coord::Scalar(b)) => a * b,
            (Coord::Tuple(xs), Coord::Tuple(ys)) => xs
                .iter()
                .zip(ys.iter())
                .map(|(x, y)| x.inner_product(y))
                .sum(),
            _ => unreachable!("invariant broken: Coords must be congruent")
        }
    }

    #[congruent(result)]
    pub fn zero_like(&self) -> Self {
        Self::zero_from_shape(&self.shape())
    }

    #[weakly_congruent(other)]
    pub fn weak_product(&self, other: &Self) -> Self {
        if self.is_congruent_to(other) {
            return Coord::Scalar(self.inner_product(other));
        }

        match (self, other) {
            (Coord::Scalar(a), Coord::Tuple(ys)) => {
                Coord::Tuple(
                    ys.iter()
                        .map(|y| Coord::Scalar(*a).weak_product(y))
                        .collect()
                )
            },
            (Coord::Tuple(xs), Coord::Tuple(ys)) => {
                assert_eq!(self.rank(), other.rank());

                let products: Vec<Coord> = xs.iter()
                    .zip(ys.iter())
                    .map(|(x, y)| x.weak_product(y))
                    .collect();

                let first = &products[0];
                if products.iter().all(|x| x.is_congruent_to(first)) {
                    let zero = first.zero_like();
                    products.into_iter().fold(zero, |acc, p| acc.sum(&p))
                } else {
                    Coord::Tuple(products)
                }
            },
            _ => unreachable!("invariant broken: self must be weakly congruent to other")
        }
    }

    #[requires(congruent(other))]
    pub fn is_strictly_inside(&self, other: &Self) -> bool {
        match (self, other) {
            (Coord::Scalar(a), Coord::Scalar(b)) => a < b,
            (Coord::Tuple(xs), Coord::Tuple(ys)) => {
                // () is not strictly inside ()
                if xs.is_empty() { return false; }
                xs.iter().zip(ys.iter()).all(|(x, y)| x.is_strictly_inside(y))
            },
            _ => unreachable!("invariant broken: Coords must be congruent")
        }
    }
}

impl From<i64> for Coord {
    fn from(x: i64) -> Self {
        Coord::Scalar(x)
    }
}

impl From<()> for Coord {
    fn from(_: ()) -> Self {
        Coord::Tuple(vec![])
    }
}

impl<A: Into<Coord>> From<(A,)> for Coord {
    fn from((a,): (A,)) -> Self {
        Coord::Tuple(vec![
            a.into(),
        ])
    }
}

impl<A: Into<Coord>,B: Into<Coord>> From<(A,B)> for Coord {
    fn from((a, b): (A, B)) -> Self {
        Coord::Tuple(vec![
            a.into(),
            b.into(),
        ])
    }
}

impl<A: Into<Coord>, B: Into<Coord>, C: Into<Coord>> From<(A,B,C)> for Coord {
    fn from((a, b, c): (A, B, C)) -> Self {
        Coord::Tuple(vec![
            a.into(),
            b.into(),
            c.into(),
        ])
    }
}

impl<A: Into<Coord>, B: Into<Coord>, C: Into<Coord>, D: Into<Coord>> From<(A,B,C,D)> for Coord {
    fn from((a, b, c, d): (A, B, C, D)) -> Self {
        Coord::Tuple(vec![
            a.into(),
            b.into(),
            c.into(),
            d.into(),
        ])
    }
}

#[cfg(test)]
mod tests {
    use super::Coord;

    #[test]
    fn rank_scalar() {
        let a: Coord = 7.into();
        let expected = 1;
        assert_eq!(a.rank(), expected);
    }

    #[test]
    fn rank_tuple() {
        let a: Coord = (1, (2, (3, 4))).into();
        let expected = 2;
        assert_eq!(a.rank(), expected);
    }

    #[test]
    fn rank_empty_tuple() {
        let a: Coord = ().into();
        let expected = 0;
        assert_eq!(a.rank(), expected);
    }

    #[test]
    fn congruent_scalars() {
        let a: Coord = 1.into();
        let b: Coord = 42.into();
        assert!(a.is_congruent_to(&b));
    }

    #[test]
    fn congruent_flat_tuples() {
        let a: Coord = (1, 2).into();
        let b: Coord = (10, 20).into();
        assert!(a.is_congruent_to(&b));
    }

    #[test]
    fn nested_congruence() {
        let a: Coord = (1, (2, 3)).into();
        let b: Coord = (9, (8, 7)).into();
        assert!(a.is_congruent_to(&b));
    }

    #[test]
    fn non_congruent_mismatched_nesting() {
        let a: Coord = 1.into();
        let b: Coord = (1, 2).into();
        assert!(!a.is_congruent_to(&b));
    }

    #[test]
    fn non_congruent_tuple_lengths() {
        let a: Coord = (1, 2).into();
        let b: Coord = 1.into();
        assert!(!a.is_congruent_to(&b));
    }

    #[test]
    fn deeply_nested_congruence() {
        let a: Coord = (1, (2, (3, 4))).into();
        let b: Coord = (10, (20, (30, 40))).into();
        assert!(a.is_congruent_to(&b));
    }

    #[test]
    fn sum_scalars() {
        let a: Coord = 3.into();
        let b: Coord = 4.into();
        let expected: Coord = 7.into();
        assert_eq!(a.sum(&b), expected);
    }

    #[test]
    fn sum_empty_tuples() {
        let a: Coord = ().into();
        let b: Coord = ().into();
        let expected: Coord = ().into();
        assert_eq!(a.sum(&b), expected);
    }

    #[test]
    fn sum_nested_tuples() {
        let a: Coord = (1, (2, 3)).into();
        let b: Coord = (4, (5, 6)).into();
        let expected: Coord = (5, (7, 9)).into();
        assert_eq!(a.sum(&b), expected);
    }

    #[test]
    fn sum_deeply_nested_tuples() {
        let a: Coord = (1, (2, (3, 4))).into();
        let b: Coord = (10, (20, (30, 40))).into();
        let expected: Coord = (11, (22, (33, 44))).into();
        assert_eq!(a.sum(&b), expected);
    }

    #[test]
    #[should_panic(expected = "Precondition failed")]
    fn sum_incongruent_scalar_and_tuple_panics() {
        let a: Coord = 1.into();
        let b: Coord = (1, 2).into();
        let _ = a.sum(&b); // should panic
    }

    #[test]
    #[should_panic(expected = "Precondition failed")]
    fn sum_incongruent_tuple_lengths_panics() {
        let a: Coord = (1, 2, 3).into();
        let b: Coord = (4, 5).into();
        let _ = a.sum(&b); // should panic
    }

    #[test]
    fn difference_scalars() {
        let a: Coord = 10.into();
        let b: Coord = 4.into();
        assert_eq!(a.difference(&b), 6.into());
    }
    
    #[test]
    fn difference_nested() {
        let a: Coord = (10, (20, 30)).into();
        let b: Coord = (1, (2, 3)).into();
        let expected: Coord = (9, (18, 27)).into();
        assert_eq!(a.difference(&b), expected);
    }
    
    #[test]
    fn difference_deeply_nested() {
        let a: Coord = (100, (50, (20, 10))).into();
        let b: Coord = (1, (2, (3, 4))).into();
        let expected: Coord = (99, (48, (17, 6))).into();
        assert_eq!(a.difference(&b), expected);
    }

    #[test]
    fn difference_empty_tuples() {
        let a: Coord = ().into();
        let b: Coord = ().into();
        let expected: Coord = ().into();
        assert_eq!(a.difference(&b), expected);
    }
    
    #[test]
    #[should_panic(expected = "Precondition failed")]
    fn difference_shape_mismatch_panics() {
        let a: Coord = (1, 2).into();
        let b: Coord = 3.into();
        let _ = a.difference(&b);
    }

    #[test]
    fn inner_product_scalars() {
        let a: Coord = 6.into();
        let b: Coord = 7.into();
        assert_eq!(a.inner_product(&b), 42);
    }
    
    #[test]
    fn inner_product_flat_tuple() {
        let a: Coord = (1, 2, 3).into();
        let b: Coord = (4, 5, 6).into();
        // 1*4 + 2*5 + 3*6 = 32
        assert_eq!(a.inner_product(&b), 32);
    }
    
    #[test]
    fn inner_product_nested() {
        let a: Coord = (1, (2, 3)).into();
        let b: Coord = (10, (20, 30)).into();
        // 1*10 + 2*20 + 3*30 = 10 + 40 + 90 = 140
        assert_eq!(a.inner_product(&b), 140);
    }
    
    #[test]
    fn inner_product_deeply_nested() {
        let a: Coord = (1, (2, (3, 4))).into();
        let b: Coord = (10, (20, (30, 40))).into();
        // 1*10 + 2*20 + 3*30 + 4*40 = 10 + 40 + 90 + 160 = 300
        assert_eq!(a.inner_product(&b), 300);
    }
    
    #[test]
    fn inner_product_empty_tuples() {
        let a = Coord::Tuple(vec![]);
        let b = Coord::Tuple(vec![]);
        assert_eq!(a.inner_product(&b), 0);
    }
    
    #[test]
    #[should_panic(expected = "Precondition failed")]
    fn inner_product_mismatched_shapes_panics() {
        let a: Coord = (1, 2).into();
        let b: Coord = 3.into();
        let _ = a.inner_product(&b);
    }

    #[test]
    fn weak_congruence_scalar_scalar() {
        let a: Coord = 1.into();
        let b: Coord = 2.into();
        assert!(a.is_weakly_congruent_to(&b));
    }
    
    #[test]
    fn weak_congruence_tuple_vs_scalar_length_1() {
        let a: Coord = (1,).into();
        let b: Coord = 1.into();
        assert!(!a.is_weakly_congruent_to(&b));
        assert!(b.is_weakly_congruent_to(&a));
    }
    
    #[test]
    fn weak_congruence_scalar_vs_tuple_length_2() {
        let a: Coord = 1.into();
        let b: Coord = (1, 2).into();
        assert!(a.is_weakly_congruent_to(&b));
        assert!(!b.is_weakly_congruent_to(&a));
    }
    
    #[test]
    fn weak_congruence_scalar_vs_tuple_length_3() {
        let a: Coord = 1.into();
        let b: Coord = (1, 2, 3).into();
        assert!(a.is_weakly_congruent_to(&b));
        assert!(!b.is_weakly_congruent_to(&a));
    }
    
    #[test]
    fn weak_congruence_tuple_vs_nested_tuple() {
        let a: Coord = (1, 2).into();
        let b: Coord = (1, (2, 3)).into();
        assert!(a.is_weakly_congruent_to(&b));
        assert!(!b.is_weakly_congruent_to(&a));
    }
    
    #[test]
    fn weak_congruence_equally_structured_tuples() {
        let a: Coord = (1, 2, 3).into();
        let b: Coord = (4, 5, 6).into();
        assert!(a.is_weakly_congruent_to(&b));
        assert!(b.is_weakly_congruent_to(&a));
    }
    
    #[test]
    fn weak_congruence_deeply_nested_asymmetric() {
        let a: Coord = (1, (2, 3, 4)).into();
        let b: Coord = ((1, 2, 3), (4, 5, 6)).into();
        assert!(a.is_weakly_congruent_to(&b));
        assert!(!b.is_weakly_congruent_to(&a));
    }
    
    #[test]
    fn weak_congruence_mismatched_tuple_lengths() {
        let a: Coord = (1, 2).into();
        let b: Coord = (1, 2, 3).into();
        assert!(!a.is_weakly_congruent_to(&b));
    }

    #[test]
    fn weak_congruence_empty_tuples() {
        let a = Coord::Tuple(vec![]);
        let b = Coord::Tuple(vec![]);
        assert!(a.is_weakly_congruent_to(&b));
    }

    #[test]
    fn weak_product_scalar_scalar_returns_scalar() {
        let a: Coord = 3.into();
        let b: Coord = 2.into();
        let expected: Coord = 6.into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_scalar_tuple_returns_scaled_tuple() {
        let a: Coord = 2.into();
        let b: Coord = (1, 2, 3).into();
        let expected: Coord = (2, 4, 6).into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_congruent_flat_tuples_returns_scalar_sum() {
        let a: Coord = (4, 5, 6).into();
        let b: Coord = (1, 2, 3).into();
        let expected: Coord = 32.into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_congruent_nested_tuples_returns_scalar_sum() {
        let a: Coord = (4, (5, 6)).into();
        let b: Coord = (1, (2, 3)).into();
        let expected: Coord = 32.into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_empty_tuples_returns_zero() {
        let a: Coord = ().into();
        let b: Coord = ().into();
        let expected: Coord = 0.into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_scalar_deep_tuple_broadcasts_correctly() {
        let a: Coord = 4.into();
        let b: Coord = (1, (2, 3)).into();
        let expected: Coord = (4, (8, 12)).into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_deep_congruent_tuples_returns_scalar_sum() {
        let a: Coord = (5, (6, (7, 8))).into();
        let b: Coord = (1, (2, (3, 4))).into();
        let expected: Coord = 70.into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_partially_congruent_tuples_returns_tuple_of_sums() {
        let a: Coord = ((1, 2), (3, 4)).into();
        let b: Coord = (((5, 6), (7, 8)), ((9, 10), (11, 12))).into();
        let expected: Coord = (90, 100).into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_scalar_vs_mixed_nested_tuple() {
        let a: Coord = (1, (2, 3)).into();
        let b: Coord = (1, ((2, 2), (3, 3))).into();
        let expected: Coord = (1, (13, 13)).into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_mixed_structures_partial_reduction() {
        let a: Coord = (1, (2, 3), (4, 5)).into();
        let b: Coord = (1, ((2, 2), (3, 3)), (4, 5)).into();
        let expected: Coord = (1, (13, 13), 41).into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_nested_mixed_with_scalars_and_tuples() {
        let a: Coord = (5, (6, 7)).into();
        let b: Coord = (1, (2, (3, 4))).into();
        let expected: Coord = (5, (12, (21, 28))).into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_tuple_with_empty_tuple_element() {
        let a: Coord = ((), 2).into();
        let b: Coord = ((), 3).into();
        let expected: Coord = 6.into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_deeply_nested_with_empty_tuple_branches() {
        let a: Coord = ((), (6, ((), 8))).into();
        let b: Coord = ((), (2, ((), 4))).into();
        let expected: Coord = 44.into();
        assert_eq!(expected, a.weak_product(&b));
    }
    
    #[test]
    fn weak_product_structurally_irregular_nested_tuples() {
        let a: Coord = (1, (2, 3), 4, 5).into();
        let b: Coord = (6, (7, (8, 9)), 10, 11).into();
        let expected: Coord = (6, (14, (24, 27)), 40, 55).into();
        assert_eq!(expected, a.weak_product(&b));
    }


    #[test]
    fn is_strictly_inside_empty_tuple() {
        let a: Coord = ().into();
        let b: Coord = ().into();
        assert!(!a.is_strictly_inside(&b));
        assert!(!b.is_strictly_inside(&a));
    }

    #[test]
    fn is_strictly_inside_scalar() {
        let a: Coord = 1.into();
        let b: Coord = 2.into();
        assert!(a.is_strictly_inside(&b));
        assert!(!b.is_strictly_inside(&a));
    }
    
    #[test]
    fn is_strictly_inside_equal_scalars() {
        let a: Coord = 5.into();
        let b: Coord = 5.into();
        assert!(!a.is_strictly_inside(&b));
    }
    
    #[test]
    fn is_strictly_inside_flat_tuple() {
        let a: Coord = (1, 2, 3).into();
        let b: Coord = (2, 3, 4).into();
        assert!(a.is_strictly_inside(&b));
        assert!(!b.is_strictly_inside(&a));
    }
    
    #[test]
    fn is_strictly_inside_nested_tuple() {
        let a: Coord = ((1, 2), 3).into();
        let b: Coord = ((2, 3), 4).into();
        assert!(a.is_strictly_inside(&b));
        assert!(!b.is_strictly_inside(&a));
    }
    
    #[test]
    fn is_strictly_inside_fails_if_any_element_not_below() {
        let a: Coord = (1, 5, 3).into();
        let b: Coord = (2, 4, 4).into();
        assert!(!a.is_strictly_inside(&b));
    }
    
    #[test]
    #[should_panic(expected = "Precondition failed")]
    fn is_strictly_inside_non_congruent_should_panic() {
        let a: Coord = (1, 2).into();
        let b: Coord = 3.into();
        let _ = a.is_strictly_inside(&b);
    }
}
