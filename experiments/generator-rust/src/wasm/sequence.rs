use super::natural::{self, Natural};

/// Boxing the entire cell also permits recursive ASTs in the head position.
pub enum Sequence<T> {
    Empty,
    Cons(Box<(T, Sequence<T>)>),
}

pub fn cons<T>(value: T, tail: Sequence<T>) -> Sequence<T> {
    Sequence::Cons(Box::new((value, tail)))
}

pub fn append<T>(left: Sequence<T>, right: Sequence<T>) -> Sequence<T> {
    match left {
        Sequence::Empty => right,
        Sequence::Cons(cell) => {
            let (head, tail): (T, Sequence<T>) = *cell;
            cons(head, append(tail, right))
        }
    }
}

pub fn snoc<T>(values: Sequence<T>, value: T) -> Sequence<T> {
    append(values, cons(value, Sequence::Empty))
}

pub fn length<T>(values: &Sequence<T>) -> Natural {
    match values {
        Sequence::Empty => Natural::Zero,
        Sequence::Cons(cell) => natural::increment(length(&cell.1)),
    }
}

pub fn get<T>(values: &Sequence<T>, index: Natural) -> Option<&T> {
    match values {
        Sequence::Empty => None,
        Sequence::Cons(cell) => match natural::decrement(index) {
            None => Some(&cell.0),
            Some(previous) => get(&cell.1, previous),
        },
    }
}

pub fn select<T>(values: Sequence<T>, index: Natural) -> Option<T> {
    match values {
        Sequence::Empty => None,
        Sequence::Cons(cell) => {
            let (head, tail): (T, Sequence<T>) = *cell;
            match natural::decrement(index) {
                None => Some(head),
                Some(previous) => select(tail, previous),
            }
        }
    }
}

pub fn last<T>(values: &Sequence<T>) -> Option<&T> {
    match values {
        Sequence::Empty => None,
        Sequence::Cons(cell) => match &cell.1 {
            Sequence::Empty => Some(&cell.0),
            Sequence::Cons(_) => last(&cell.1),
        },
    }
}

/// A missing prefix is explicit; splitting never truncates a requested count.
pub fn split_at<T>(values: Sequence<T>, count: Natural) -> Option<(Sequence<T>, Sequence<T>)> {
    match natural::decrement(count) {
        None => Some((Sequence::Empty, values)),
        Some(previous) => match values {
            Sequence::Empty => None,
            Sequence::Cons(cell) => {
                let (head, tail): (T, Sequence<T>) = *cell;
                match split_at(tail, previous) {
                    None => None,
                    Some((prefix, suffix)) => Some((cons(head, prefix), suffix)),
                }
            }
        },
    }
}

fn reverse_into<T>(values: Sequence<T>, output: Sequence<T>) -> Sequence<T> {
    match values {
        Sequence::Empty => output,
        Sequence::Cons(cell) => {
            let (head, tail): (T, Sequence<T>) = *cell;
            reverse_into(tail, cons(head, output))
        }
    }
}

pub fn reverse<T>(values: Sequence<T>) -> Sequence<T> {
    reverse_into(values, Sequence::Empty)
}
