use crate::{congruent, requires, weakly_congruent};
use crate::shape::Shape;

fn exclusive_scan<T,F>(xs: &[T], init: T, op: F) -> Vec<T>
where
    F: Fn(T, T) -> T,
    T: Copy,
{
    let mut acc = init;
    let mut result = Vec::with_capacity(xs.len() + 1);
    for &x in xs {
        result.push(acc);
        acc = op(acc, x);
    }
    result.push(acc);
    result
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Coord {
    Scalar(i64),
    Tuple(Vec<Coord>),
}

impl Coord {
    pub fn new_with_shape(flat: &[i64], shape: Shape) -> Self {
        fn build(shape: &Shape, flat: &[i64], idx: &mut usize) -> Coord {
            match shape {
                Shape::Scalar => {
                    let i = *idx;
                    assert!(i < flat.len(), "not enough elements to unflatten Coord");
                    *idx += 1;
                    Coord::Scalar(flat[i])
                }
                Shape::Tuple(children) => {
                    let mut coords = Vec::with_capacity(children.len());
                    for child_shape in children {
                        coords.push(build(child_shape, flat, idx));
                    }
                    Coord::Tuple(coords)
                }
            }
        }

        let mut idx = 0;
        let coord = build(&shape, flat, &mut idx);
        assert!(idx == flat.len(),
            "too many elements in flat slice for given Shape: consumed {idx}, had {}",
            flat.len(),
        );
        coord
    }

    pub fn unflatten_like(flat: &[i64], coord: &Self) -> Self {
        Self::new_with_shape(flat, coord.shape())
    }

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

    pub fn size(&self) -> i64 {
        match self {
            Coord::Scalar(n) => *n,
            Coord::Tuple(elements) => elements.iter().map(|e| e.size()).product(),
        }
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
                xs.iter().zip(ys.iter()).all(|(x, y)| x.is_strictly_inside(y))
            },
            _ => unreachable!("invariant broken: Coords must be congruent")
        }
    }

    #[requires(congruent(other))]
    pub fn is_inside(&self, other: &Self) -> bool {
        match (self, other) {
            (Coord::Scalar(a), Coord::Scalar(b)) => a <= b,
            (Coord::Tuple(xs), Coord::Tuple(ys)) => {
                xs.iter().zip(ys.iter()).all(|(x, y)| x.is_inside(y))
            },
            _ => unreachable!("invariant broken: Coords must be congruent")
        }
    }

    pub fn to_flat_tuple(&self) -> Vec<i64> {
        match self {
            Coord::Scalar(x) => vec![*x],
            Coord::Tuple(xs) =>
                xs.iter()
                    .flat_map(|c| c.to_flat_tuple())
                    .collect(),
                
        }
    }

    pub fn zero_extend_to_shape(&self, shape: &Shape) -> Self {
        match (self, shape) {
            (Coord::Scalar(x), Shape::Scalar) => Coord::Scalar(*x),

            (Coord::Scalar(_), Shape::Tuple(children)) => {
                let mut iter = children.iter();
                Coord::Tuple(
                    std::iter::once(self.zero_extend_to_shape(iter.next().unwrap()))
                        .chain(iter.map(Coord::zero_from_shape))
                        .collect()
                )
            },

            (Coord::Tuple(xs), Shape::Tuple(children)) => {
                assert_eq!(xs.len(), children.len(),
                    "Coord::zero_extend_to_shape: tuple arity mismatch"
                );
                Coord::Tuple(
                    xs.iter()
                        .zip(children)
                        .map(|(x, child_shape)| x.zero_extend_to_shape(child_shape))
                        .collect()
                )
            },

            (Coord::Tuple(_), Shape::Scalar) => {
                unreachable!("precondition violated: tuple cannot extend to scalar")
            }
        }
    }

    #[requires(weakly_congruent(other))]
    pub fn zero_extend_like(&self, other: &Coord) -> Self {
        self.zero_extend_to_shape(&other.shape())
    }

    #[requires(weakly_congruent(shape))]
    pub fn colexicographical_lift(&self, shape: &Coord) -> Coord {
        match (self, shape) {
            (Coord::Scalar(x), _) => {
                let mut flat_shape = shape.to_flat_tuple();
                flat_shape.pop(); // the final element is irrelevant

                let mut scanned = exclusive_scan(&flat_shape, 1, |a, b| a * b);
                let total_product = scanned.pop().unwrap();
                let prefix_products = scanned;

                let mut result: Vec<i64> = prefix_products
                    .iter()
                    .zip(&flat_shape)
                    .map(|(&p, &d)| (x / p) % d)
                    .collect();

                result.push(x / total_product);

                Coord::unflatten_like(&result, &shape)
            }

            (Coord::Tuple(xs), Coord::Tuple(ys)) => {
                assert_eq!(xs.len(), ys.len(), "precondition violated: tuple arity mismatch");
                Coord::Tuple(
                    xs.iter()
                        .zip(ys)
                        .map(|(x, y)| x.colexicographical_lift(y))
                        .collect()
                )
            }

            (Coord::Tuple(_), Coord::Scalar(_)) => {
                unreachable!("precondition violated: tuple cannot lift to scalar")
            }
        }
    }

    pub fn compact_left_major_stride_for(shape: &Self) -> Self {
        Self::compact_left_major_stride_impl(shape, 1)
    }

    fn compact_left_major_stride_impl(shape: &Coord, prev_product: i64) -> Self {
        match shape {
            Coord::Scalar(_) => Coord::Scalar(prev_product),
            Coord::Tuple(elements) => {
                let mut result = Vec::new();
                let mut current_product = prev_product;
                for elem in elements {
                    result.push(Self::compact_left_major_stride_impl(elem, current_product));
                    current_product *= elem.size();
                }
                Coord::Tuple(result)
            }
        }
    }

    /// Iterate over all coordinates in colexicographical order from zero to shape (exclusive).
    pub fn colex_iter_for(shape: &Coord) -> ColexIter {
        ColexIter {
            current: shape.zero_like(),
            end: shape.clone(),
            done: shape.size() == 0,
        }
    }

    /// Increment in colexicographical order. Returns true if rolled over past the end.
    fn colex_increment(&mut self, end: &Coord) -> bool {
        match (self, end) {
            (Coord::Scalar(x), Coord::Scalar(bound)) => {
                *x += 1;
                *x >= *bound
            }
            (Coord::Tuple(xs), Coord::Tuple(bounds)) => {
                if xs.is_empty() {
                    return true; // nullary always rolls over
                }
                for i in 0..xs.len() {
                    if !xs[i].colex_increment(&bounds[i]) {
                        return false;
                    }
                    if i < xs.len() - 1 {
                        xs[i] = bounds[i].zero_like();
                    }
                }
                true
            }
            _ => unreachable!("Coord and end must be congruent")
        }
    }
}

pub struct ColexIter {
    current: Coord,
    end: Coord,
    done: bool,
}

impl Iterator for ColexIter {
    type Item = Coord;

    fn next(&mut self) -> Option<Self::Item> {
        if self.done {
            return None;
        }

        let result = self.current.clone();
        self.done = self.current.colex_increment(&self.end);
        Some(result)
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
    fn to_flat_tuple_scalar() {
        let a: Coord = 7.into();
        let flat = a.to_flat_tuple();
        assert_eq!(flat, vec![7]);
    }

    #[test]
    fn to_flat_tuple_empty_tuple() {
        let a: Coord = ().into();
        let flat = a.to_flat_tuple();
        assert_eq!(flat, Vec::<i64>::new());
    }

    #[test]
    fn to_flat_tuple_flat_tuple() {
        let a: Coord = (1, 2, 3).into();
        let flat = a.to_flat_tuple();
        assert_eq!(flat, vec![1, 2, 3]);
    }

    #[test]
    fn to_flat_tuple_nested_tuple() {
        let a: Coord = (1, (2, 3)).into();
        let flat = a.to_flat_tuple();
        assert_eq!(flat, vec![1, 2, 3]);
    }

    #[test]
    fn to_flat_tuple_deeply_nested_tuple() {
        let a: Coord = (1, (2, (3, 4))).into();
        let flat = a.to_flat_tuple();
        assert_eq!(flat, vec![1, 2, 3, 4]);
    }

    #[test]
    fn to_flat_tuple_mixed_with_empty_tuple() {
        let a: Coord = ((), 2, ((), 3)).into();
        let flat = a.to_flat_tuple();
        assert_eq!(flat, vec![2, 3]);
    }

    #[test]
    fn to_flat_tuple_complex_nested_structure() {
        let a: Coord = ((1, (2, ())), ((), (3, 4))).into();
        let flat = a.to_flat_tuple();
        assert_eq!(flat, vec![1, 2, 3, 4]);
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
        assert!(a.is_strictly_inside(&b));
        assert!(b.is_strictly_inside(&a));
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

    #[test]
    fn is_inside_empty_tuple() {
        let a: Coord = ().into();
        let b: Coord = ().into();
        assert!(a.is_inside(&b));
    }

    #[test]
    fn is_inside_scalar_lt() {
        let a: Coord = 1.into();
        let b: Coord = 2.into();
        assert!(a.is_inside(&b));
        assert!(!b.is_inside(&a));
    }

    #[test]
    fn is_inside_scalar_eq() {
        let a: Coord = 5.into();
        let b: Coord = 5.into();
        assert!(a.is_inside(&b));
    }


    #[test]
    fn is_inside_scalar_gt() {
        let a: Coord = 7.into();
        let b: Coord = 3.into();
        assert!(!a.is_inside(&b));
        assert!(b.is_inside(&a));
    }


    #[test]
    fn is_inside_flat_tuple_all_lt() {
        let a: Coord = (1, 2, 3).into();
        let b: Coord = (2, 3, 4).into();
        assert!(a.is_inside(&b));
        assert!(!b.is_inside(&a));
    }

    #[test]
    fn is_inside_flat_tuple_with_equals() {
        let a: Coord = (1, 2, 3).into();
        let b: Coord = (1, 3, 3).into(); // equal on 0 and 2
        assert!(a.is_inside(&b));
        assert!(!b.is_inside(&a));
    }

    #[test]
    fn is_inside_nested_tuple_all_le() {
        let a: Coord = ((1, 2), 3).into();
        let b: Coord = ((1, 3), 3).into(); // equal last, others a<=b
        assert!(a.is_inside(&b));
        assert!(!b.is_inside(&a));
    }

    #[test]
    fn is_inside_nested_tuple_fails_on_one_position() {
        let a: Coord = ((2, 5), 3).into();
        let b: Coord = ((2, 4), 4).into(); // 5 <= 4 fails
        assert!(!a.is_inside(&b));
    }

    #[test]
    fn is_inside_tuple_with_empty_element() {
        let a: Coord = ((), 2).into();
        let b: Coord = ((), 2).into();
        assert!(a.is_inside(&b));
        assert!(b.is_inside(&a));
    }

    #[test]
    fn is_inside_deep_nested_with_empties() {
        let a: Coord = ((), (2, ((), 3))).into();
        let b: Coord = ((), (2, ((), 4))).into();
        assert!(a.is_inside(&b));   // equal on empties/2; 3 <= 4
        assert!(!b.is_inside(&a));  // 4 <= 3 fails
    }

    #[test]
    #[should_panic(expected = "Precondition failed")]
    fn is_inside_non_congruent_should_panic() {
        let a: Coord = (1, 2).into();
        let b: Coord = 3.into();
        let _ = a.is_inside(&b);
    }

    #[test]
    fn flatten_unflatten_roundtrip() {
        let cases: &[Coord] = &[
            7.into(),
            ().into(),
            (1,).into(),
            (1, 2).into(),
            (1, (2, 3)).into(),
            (1, (2, (3, 4))).into(),
            ((), 2, ((), 3)).into(),
            ((1, (2, ())), ((), (3, 4))).into(),
        ];

        for original in cases {
            let flat = original.to_flat_tuple();
            let shape = original.shape();
            let reconstructed = Coord::new_with_shape(&flat, shape);
            assert_eq!(
                *original, reconstructed,
                "round-trip failed for {original:?}"
            );
        }
    }

    #[test]
    fn unflatten_like_matches_new_with_shape() {
        let like: Coord = (1, (2, 3)).into();
        let flat = vec![10, 20, 30];
    
        let a = Coord::new_with_shape(&flat, like.shape());
        let b = Coord::unflatten_like(&flat, &like);
    
        assert_eq!(a, b);
    }

    #[test]
    fn colex_lift_congruent_is_identity() {
        let a: Coord = (1, (2, 3)).into();
        let shape: Coord = (10, (20, 30)).into();
        let expected = a.clone();
        let result = a.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_empty_tuple() {
        let coord: Coord = ().into();
        let shape: Coord = ().into();
        let expected: Coord = ().into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_pair_of_empty_tuple() {
        let coord: Coord = ((), ()).into();
        let shape: Coord = ((), ()).into();
        let expected: Coord = ((), ()).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_scalar() {
        let coord: Coord = 5.into();
        let shape: Coord = 10.into();
        let expected: Coord = 5.into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_scalar_into_single() {
        let coord: Coord = 5.into();
        let shape: Coord = (10,).into();
        let expected: Coord = (5,).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_scalar_into_pair() {
        let coord: Coord = 23.into();
        let shape: Coord = (5,5).into();
        let expected: Coord = (3,4).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_scalar_into_triple() {
        let coord: Coord = 1234.into();
        let shape: Coord = (2,3,5).into();
        let expected: Coord = (0,2,205).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_scalar_into_quadruple() {
        let coord: Coord = 1234.into();
        let shape: Coord = (2,3,5,7).into();
        let expected: Coord = (0,2,0,41).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_complex_nested() {
        let coord: Coord    = (    1, (      2, (3,        4))).into();
        let shape: Coord    = ((1,2), ((2,2,2), (3,(4,4,4,4)))).into();
        let expected: Coord = ((0,1), ((0,1,0), (3,(0,1,0,0)))).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_scalar_into_nested_pair() {
        let coord: Coord = 23.into();
        let shape: Coord = ((5, 5),).into();
        let expected: Coord = ((3, 4),).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_scalar_into_deeply_nested() {
        let coord: Coord = 23.into();
        let shape: Coord = (5, (5,)).into();
        let expected: Coord = (3, (4,)).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_pair_into_pair_of_pairs() {
        let coord: Coord = (7, 23).into();
        let shape: Coord = ((2, 4), (5, 5)).into();
        let expected: Coord = ((1, 3), (3, 4)).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_large_overflow() {
        let coord: Coord = 1000.into();
        let shape: Coord = (2, 2).into();
        // 1000 % 2 = 0, 1000 / 2 = 500
        let expected: Coord = (0, 500).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_nested_with_single_element_tuples() {
        let coord: Coord = (5, (7,)).into();
        let shape: Coord = ((2, 3), ((2, 4),)).into();
        // 5 into (2, 3): 5 % 2 = 1, 5 / 2 = 2 → (1, 2)
        // 7 into (2, 4): 7 % 2 = 1, 7 / 2 = 3 → (1, 3)
        let expected: Coord = ((1, 2), ((1, 3),)).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_lift_shape_with_ones() {
        let coord: Coord = 7.into();
        let shape: Coord = (1, 1, 10).into();
        // 7 % 1 = 0, 7 / 1 = 7
        // 7 % 1 = 0, 7 / 1 = 7
        // final: 7
        let expected: Coord = (0, 0, 7).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }
    
    #[test]
    fn colex_lift_scalar_into_triple_nested() {
        let coord: Coord = 23.into();
        let shape: Coord = (((5, 5),),).into();
        let expected: Coord = (((3, 4),),).into();
        let result = coord.colexicographical_lift(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn compact_left_major_stride_for_scalar() {
        let shape: Coord = 10.into();
        let expected: Coord = 1.into();
        let result = Coord::compact_left_major_stride_for(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn compact_left_major_stride_for_empty_tuple() {
        let shape: Coord = ().into();
        let expected: Coord = ().into();
        let result = Coord::compact_left_major_stride_for(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn compact_left_major_stride_for_flat_tuple() {
        // shape: (2, 3, 4)
        let shape: Coord = (2, 3, 4).into();

        // compact left-major strides: (1, 2, 2*3) = (1, 2, 6)
        let expected: Coord = (1, 2, 6).into();

        let result = Coord::compact_left_major_stride_for(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn compact_left_major_stride_for_nested() {
        // shape: (2, (3, 4))
        let shape: Coord = (2, (3, 4)).into();

        // left-major (row-major) compact strides:
        // first element stride = 1
        // second element is a tuple, so its children start at product(2) = 2:
        //   stride(3) = 2
        //   stride(4) = 2 * 3 = 6
        let expected: Coord = (1, (2, 6)).into();

        let result = Coord::compact_left_major_stride_for(&shape);
        assert_eq!(expected, result);
    }

    #[test]
    fn colex_iter_for_scalar() {
        let shape: Coord = 3.into();
        let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
        assert_eq!(coords, vec![0.into(), 1.into(), 2.into()]);
    }
    
    #[test]
    fn colex_iter_for_scalar_zero() {
        let shape: Coord = 0.into();
        let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
        assert!(coords.is_empty());
    }
    
    #[test]
    fn colex_iter_for_scalar_one() {
        let shape: Coord = 1.into();
        let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
        assert_eq!(coords, vec![0.into()]);
    }
    
    #[test]
    fn colex_iter_for_pair() {
        let shape: Coord = (2, 3).into();
        let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
        let expected: Vec<Coord> = vec![
            (0, 0).into(),
            (1, 0).into(),
            (0, 1).into(),
            (1, 1).into(),
            (0, 2).into(),
            (1, 2).into(),
        ];
        assert_eq!(coords, expected);
    }
    
    #[test]
    fn colex_iter_for_pair_first_dim_one() {
        let shape: Coord = (1, 3).into();
        let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
        let expected: Vec<Coord> = vec![
            (0, 0).into(),
            (0, 1).into(),
            (0, 2).into(),
        ];
        assert_eq!(coords, expected);
    }
    
    #[test]
    fn colex_iter_for_pair_second_dim_one() {
        let shape: Coord = (3, 1).into();
        let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
        let expected: Vec<Coord> = vec![
            (0, 0).into(),
            (1, 0).into(),
            (2, 0).into(),
        ];
        assert_eq!(coords, expected);
    }
    
    #[test]
    fn colex_iter_for_triple() {
        let shape: Coord = (2, 2, 2).into();
        let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
        let expected: Vec<Coord> = vec![
            (0, 0, 0).into(),
            (1, 0, 0).into(),
            (0, 1, 0).into(),
            (1, 1, 0).into(),
            (0, 0, 1).into(),
            (1, 0, 1).into(),
            (0, 1, 1).into(),
            (1, 1, 1).into(),
        ];
        assert_eq!(coords, expected);
    }
    
    #[test]
    fn colex_iter_for_empty_tuple() {
        let shape: Coord = ().into();
        let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
        assert_eq!(coords, vec![().into()]);
    }
    
    #[test]
    fn colex_iter_for_zero_size_first_dim() {
        let shape: Coord = (0, 3).into();
        let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
        assert!(coords.is_empty());
    }
    
    #[test]
    fn colex_iter_for_zero_size_second_dim() {
        let shape: Coord = (2, 0).into();
        let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
        assert!(coords.is_empty());
    }
    
    #[test]
    fn colex_iter_for_nested() {
        let shape: Coord = (2, (2, 2)).into();
        let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
        let expected: Vec<Coord> = vec![
            (0, (0, 0)).into(),
            (1, (0, 0)).into(),
            (0, (1, 0)).into(),
            (1, (1, 0)).into(),
            (0, (0, 1)).into(),
            (1, (0, 1)).into(),
            (0, (1, 1)).into(),
            (1, (1, 1)).into(),
        ];
        assert_eq!(coords, expected);
    }
    
    #[test]
    fn colex_iter_for_count_matches_size() {
        let shapes: Vec<Coord> = vec![
            3.into(),
            (2, 3).into(),
            (2, 3, 4).into(),
            (2, (3, 4)).into(),
            ().into(),
        ];
        
        for shape in shapes {
            let count = Coord::colex_iter_for(&shape).count();
            let expected = shape.size().max(0) as usize;
            assert_eq!(count, expected, "count mismatch for shape {:?}", shape);
        }
    }

  #[test]
  fn colex_iter_for_pair_with_trailing_empty() {
      let shape: Coord = (2, ()).into();
      let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
      let expected: Vec<Coord> = vec![
          (0, ()).into(),
          (1, ()).into(),
      ];
      assert_eq!(coords, expected);
  }
  
  #[test]
  fn colex_iter_for_pair_with_leading_empty() {
      let shape: Coord = ((), 2).into();
      let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
      let expected: Vec<Coord> = vec![
          ((), 0).into(),
          ((), 1).into(),
      ];
      assert_eq!(coords, expected);
  }
  
  #[test]
  fn colex_iter_for_pair_of_empties() {
      let shape: Coord = ((), ()).into();
      let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
      let expected: Vec<Coord> = vec![
          ((), ()).into(),
      ];
      assert_eq!(coords, expected);
  }
  
  #[test]
  fn colex_iter_for_nested_with_empty() {
      let shape: Coord = (2, ((), 2)).into();
      let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
      let expected: Vec<Coord> = vec![
          (0, ((), 0)).into(),
          (1, ((), 0)).into(),
          (0, ((), 1)).into(),
          (1, ((), 1)).into(),
      ];
      assert_eq!(coords, expected);
  }
  
  #[test]
  fn colex_iter_for_nested_with_trailing_empty() {
      let shape: Coord = ((2, ()), 2).into();
      let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
      let expected: Vec<Coord> = vec![
          ((0, ()), 0).into(),
          ((1, ()), 0).into(),
          ((0, ()), 1).into(),
          ((1, ()), 1).into(),
      ];
      assert_eq!(coords, expected);
  }
  
  #[test]
  fn colex_iter_for_triple_with_middle_empty() {
      let shape: Coord = (2, (), 2).into();
      let coords: Vec<Coord> = Coord::colex_iter_for(&shape).collect();
      let expected: Vec<Coord> = vec![
          (0, (), 0).into(),
          (1, (), 0).into(),
          (0, (), 1).into(),
          (1, (), 1).into(),
      ];
      assert_eq!(coords, expected);
  }
  
  #[test]
  fn colex_iter_for_with_empty_size_matches_count() {
      let shapes: Vec<Coord> = vec![
          (2, ()).into(),
          ((), 2).into(),
          ((), ()).into(),
          (2, ((), 2)).into(),
          ((2, ()), 2).into(),
          (2, (), 2).into(),
      ];
      
      for shape in shapes {
          let count = Coord::colex_iter_for(&shape).count();
          let expected = shape.size() as usize;
          assert_eq!(count, expected, "count mismatch for shape {:?}", shape);
      }
  }
}
