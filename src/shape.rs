#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Shape {
    Scalar,
    Tuple(Vec<Shape>),
}

impl Shape {
    pub fn rank(&self) -> usize {
        match self {
            Self::Scalar => 1,
            Self::Tuple(xs) => xs.len(),
        }
    }

    pub fn is_congruent_to(&self, other: &Self) -> bool {
        match (self, other) {
            (Self::Scalar, Self::Scalar) => true,
            (Self::Tuple(xs), Self::Tuple(ys)) => {
                xs.len() == ys.len()
                    && xs.iter().zip(ys.iter()).all(|(x, y)| x.is_congruent_to(y))
            },
            _ => false,
        }
    }

    pub fn is_weakly_congruent_to(&self, other: &Self) -> bool {
        match (self, other) {
            // terminal case 0: both are scalars
            (Self::Scalar, Self::Scalar) => true,

            // terminal case 1: both are empty tuples
            (Self::Tuple(_), Self::Tuple(_)) if self.rank() == 0 && other.rank() == 0 => true,

            // recursive case 0: scalar vs non-empty tuple
            (Self::Scalar, Self::Tuple(children)) if other.rank() > 0 => {
                children.iter().all(|child| self.is_weakly_congruent_to(child))
            },

            // recursive case 1: tuples with equal non-zero rank
            (Self::Tuple(xs), Self::Tuple(ys)) if self.rank() == other.rank() && self.rank() > 0 => {
                xs.iter().zip(ys.iter()).all(|(a, b)| a.is_weakly_congruent_to(b))
            },

            // terminal case 3: all other cases are not weakly congruent
            _ => false,
        }
    }


    /// cf mlir::coord::inferWeakProductReturnType.
    /// Returns None if preconditions fail.
    pub fn weak_product_result(a: &Shape, b: &Shape) -> Option<Shape> {
        if !a.is_weakly_congruent_to(b) {
            return None;
        }
        if a.is_congruent_to(b) {
            return Some(Shape::Scalar);
        }

        // scalar ⊗ non-empty tuple => elementwise
        if matches!(a, Shape::Scalar) {
            if let Shape::Tuple(ys) = b {
                if ys.is_empty() {
                    return None;
                }
                let elems: Option<Vec<_>> =
                    ys.iter().map(|y| Shape::weak_product_result(a, y)).collect();
                return elems.map(Shape::Tuple);
            }
        }

        // tuples with equal non-zero rank => recurse pairwise
        let (Shape::Tuple(xs), Shape::Tuple(ys)) = (a, b) else { return None; };
        if xs.is_empty() || ys.is_empty() || xs.len() != ys.len() {
            return None;
        }

        let childs: Option<Vec<_>> = xs
            .iter()
            .zip(ys.iter())
            .map(|(x, y)| Shape::weak_product_result(x, y))
            .collect();
        let childs = childs?;

        // collapse if children are congruent
        let first = &childs[0];
        if childs.iter().all(|c| c.is_congruent_to(first)) {
            Some(first.clone())
        } else {
            Some(Shape::Tuple(childs))
        }
    }
}
