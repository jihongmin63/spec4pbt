/// Canonical binary naturals: every positive value has a nonzero leading bit.
pub enum Positive {
    One,
    Bit0(Box<Positive>),
    Bit1(Box<Positive>),
}

pub enum Natural {
    Zero,
    Positive(Positive),
}

fn copy_positive(value: &Positive) -> Positive {
    match value {
        Positive::One => Positive::One,
        Positive::Bit0(tail) => Positive::Bit0(Box::new(copy_positive(tail))),
        Positive::Bit1(tail) => Positive::Bit1(Box::new(copy_positive(tail))),
    }
}

pub fn copy(value: &Natural) -> Natural {
    match value {
        Natural::Zero => Natural::Zero,
        Natural::Positive(value) => Natural::Positive(copy_positive(value)),
    }
}

fn positive_from_u64(value: u64) -> Positive {
    if value <= 1 {
        Positive::One
    } else {
        let tail: Box<Positive> = Box::new(positive_from_u64(value / 2));
        if value % 2 == 0 { Positive::Bit0(tail) } else { Positive::Bit1(tail) }
    }
}

/// Bounded frontend conversion; the core representation has no word-size bound.
pub fn from_u64(value: u64) -> Natural {
    if value == 0 { Natural::Zero } else { Natural::Positive(positive_from_u64(value)) }
}

fn positive_to_u64(value: &Positive) -> Option<u64> {
    match value {
        Positive::One => Some(1),
        Positive::Bit0(tail) => {
            let prefix: u64 = match positive_to_u64(tail) {
                Some(prefix) => prefix,
                None => return None,
            };
            if prefix > u64::MAX / 2 { None } else { Some(prefix * 2) }
        }
        Positive::Bit1(tail) => {
            let prefix: u64 = match positive_to_u64(tail) {
                Some(prefix) => prefix,
                None => return None,
            };
            if prefix > u64::MAX / 2 { None } else { Some(prefix * 2 + 1) }
        }
    }
}

/// Exact partial conversion: values above the word range are reported as None.
pub fn to_u64(value: &Natural) -> Option<u64> {
    match value {
        Natural::Zero => Some(0),
        Natural::Positive(value) => positive_to_u64(value),
    }
}

fn increment_positive(value: Positive) -> Positive {
    match value {
        Positive::One => Positive::Bit0(Box::new(Positive::One)),
        Positive::Bit0(tail) => Positive::Bit1(tail),
        Positive::Bit1(tail) => Positive::Bit0(Box::new(increment_positive(*tail))),
    }
}

pub fn increment(value: Natural) -> Natural {
    match value {
        Natural::Zero => Natural::Positive(Positive::One),
        Natural::Positive(value) => Natural::Positive(increment_positive(value)),
    }
}

fn predecessor(value: Positive) -> Natural {
    match value {
        Positive::One => Natural::Zero,
        Positive::Bit0(tail) => match predecessor(*tail) {
            Natural::Zero => Natural::Positive(Positive::One),
            Natural::Positive(rest) => Natural::Positive(Positive::Bit1(Box::new(rest))),
        },
        Positive::Bit1(tail) => Natural::Positive(Positive::Bit0(tail)),
    }
}

/// Zero is reported explicitly, without wrapping or saturating the budget.
pub fn decrement(value: Natural) -> Option<Natural> {
    match value {
        Natural::Zero => None,
        Natural::Positive(value) => Some(predecessor(value)),
    }
}

fn double(value: Natural) -> Natural {
    match value {
        Natural::Zero => Natural::Zero,
        Natural::Positive(value) => Natural::Positive(Positive::Bit0(Box::new(value))),
    }
}

fn double_plus_one(value: Natural) -> Natural {
    match value {
        Natural::Zero => Natural::Positive(Positive::One),
        Natural::Positive(value) => Natural::Positive(Positive::Bit1(Box::new(value))),
    }
}

fn positive_difference(left: &Positive, right: &Positive) -> Option<Natural> {
    match (left, right) {
        (Positive::One, Positive::One) => Some(Natural::Zero),
        (Positive::One, _) => None,
        (_, Positive::One) => Some(predecessor(copy_positive(left))),
        (Positive::Bit0(left), Positive::Bit0(right))
        | (Positive::Bit1(left), Positive::Bit1(right)) => {
            match positive_difference(left, right) {
                None => None,
                Some(value) => Some(double(value)),
            }
        }
        (Positive::Bit1(left), Positive::Bit0(right)) => {
            match positive_difference(left, right) {
                None => None,
                Some(value) => Some(double_plus_one(value)),
            }
        }
        (Positive::Bit0(left), Positive::Bit1(right)) => {
            match positive_difference(left, right) {
                None => None,
                Some(value) => match decrement(value) {
                    None => None,
                    Some(previous) => Some(double_plus_one(previous)),
                },
            }
        }
    }
}

/// Subtract binary naturals exactly, reporting underflow instead of saturating.
pub fn difference(left: &Natural, right: &Natural) -> Option<Natural> {
    match (left, right) {
        (_, Natural::Zero) => Some(copy(left)),
        (Natural::Zero, Natural::Positive(_)) => None,
        (Natural::Positive(left), Natural::Positive(right)) => positive_difference(left, right),
    }
}
