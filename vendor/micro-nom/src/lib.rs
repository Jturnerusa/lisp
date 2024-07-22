#![allow(dead_code)]
#![feature(impl_trait_in_assoc_type)]

use std::ops::Range;

pub trait Input {
    type Item<'a>
    where
        Self: 'a;

    type Iter<'a>: Iterator<Item = Self::Item<'a>>
    where
        Self: 'a;

    fn slice(self, range: Range<usize>) -> Self
    where
        Self: Sized;

    fn len(self) -> usize;

    #[allow(clippy::wrong_self_convention)]
    fn is_empty(self) -> bool
    where
        Self: Sized,
    {
        self.len() == 0
    }

    fn items<'a>(self) -> Self::Iter<'a>
    where
        Self: 'a;
}

pub fn take<I>(count: usize) -> impl Fn(I) -> Result<(I, I), ()>
where
    I: Input + Clone + Copy,
{
    move |input: I| {
        if count > input.len() {
            Err(())
        } else {
            Ok((input.slice(count..input.len()), input.slice(0..count)))
        }
    }
}

#[allow(clippy::redundant_closure)]
pub fn take_while<'input, I, F>(f: F) -> impl Fn(I) -> Result<(I, I), ()>
where
    I: Input + Clone + Copy + 'input,
    F: Fn(I::Item<'input>) -> bool,
    I::Item<'input>: Clone,
{
    move |input: I| {
        let count = input.items().take_while(|i| f(i.clone())).count();
        take(count)(input)
    }
}

#[allow(clippy::redundant_closure)]
pub fn take_while1<'input, I, F>(f: F) -> impl Fn(I) -> Result<(I, I), ()>
where
    I: Input + Clone + Copy + 'input,
    F: Fn(I::Item<'input>) -> bool,
    I::Item<'input>: Clone,
{
    move |input: I| {
        let count = input.items().take_while(|i| f(i.clone())).count();
        if count < 1 {
            Err(())
        } else {
            take(count)(input)
        }
    }
}

#[allow(clippy::redundant_closure)]
pub fn take_while_m_n<'input, I, F>(m: usize, n: usize, f: F) -> impl Fn(I) -> Result<(I, I), ()>
where
    I: Input + Clone + Copy + 'input,
    F: Fn(I::Item<'input>) -> bool,
    I::Item<'input>: Clone,
{
    move |input: I| {
        let count = input.items().take_while(|i| f(i.clone())).count();

        if (m..n).contains(&count) {
            take(count)(input)
        } else {
            take(0)(input)
        }
    }
}

pub fn take_one<'input, I>(input: I) -> Result<(I, I::Item<'input>), ()>
where
    I: Input + Clone + Copy,
{
    let one = input.items().next().ok_or(())?;
    let rest = input.slice(1..input.len());
    Ok((rest, one))
}

pub fn take_one_if<'input, I, F>(f: F) -> impl Fn(I) -> Result<(I, I::Item<'input>), ()>
where
    I: Input + Clone + Copy + 'input,
    F: Fn(&I::Item<'input>) -> bool,
{
    move |input: I| {
        let (rest, one) = take_one(input)?;
        if f(&one) {
            Ok((rest, one))
        } else {
            Err(())
        }
    }
}

pub fn pair<I, O1, O2, A, B>(a: A, b: B) -> impl Fn(I) -> Result<(I, (O1, O2)), ()>
where
    I: Input + Clone + Copy,
    A: Fn(I) -> Result<(I, O1), ()>,
    B: Fn(I) -> Result<(I, O2), ()>,
{
    move |input: I| {
        let (rest, a) = a(input)?;
        let (rest, b) = b(rest)?;
        Ok((rest, (a, b)))
    }
}

pub fn separated<I, O1, O2, O3, A, B, C>(
    a: A,
    b: B,
    c: C,
) -> impl Fn(I) -> Result<(I, (O1, O3)), ()>
where
    I: Input + Clone + Copy,
    A: Fn(I) -> Result<(I, O1), ()>,
    B: Fn(I) -> Result<(I, O2), ()>,
    C: Fn(I) -> Result<(I, O3), ()>,
{
    move |input: I| {
        let (rest, a) = a(input)?;
        let (rest, _) = b(rest)?;
        let (rest, c) = c(rest)?;
        Ok((rest, (a, c)))
    }
}

pub fn map<I, O, A, F, T>(a: A, f: F) -> impl Fn(I) -> Result<(I, T), ()>
where
    I: Input + Clone + Copy,
    A: Fn(I) -> Result<(I, O), ()>,
    F: Fn(O) -> T,
{
    move |input: I| {
        let (rest, a) = a(input)?;
        Ok((rest, f(a)))
    }
}

pub fn branch<I, O, A, B>(a: A, b: B) -> impl Fn(I) -> Result<(I, O), ()>
where
    I: Input + Clone + Copy,
    A: Fn(I) -> Result<(I, O), ()>,
    B: Fn(I) -> Result<(I, O), ()>,
{
    move |input: I| {
        let first = a(input);
        let second = b(input);

        match (first, second) {
            (Ok((rest, output)), Err(_)) => Ok((rest, output)),
            (Err(_), Ok((rest, output))) => Ok((rest, output)),
            (Ok((rest, output)), Ok(..)) => Ok((rest, output)),
            _ => Err(()),
        }
    }
}

impl<I> Input for &[I] {
    type Item<'item> = &'item I where Self: 'item;

    type Iter<'iter> = impl Iterator<Item = Self::Item<'iter>> where Self: 'iter;

    fn slice(self, range: Range<usize>) -> Self
    where
        Self: Sized,
    {
        &self[range]
    }

    fn len(self) -> usize {
        self.len()
    }

    fn items<'a>(self) -> Self::Iter<'a>
    where
        Self: 'a,
    {
        self.iter()
    }
}

impl Input for &str {
    type Item<'item> = char where Self: 'item;

    type Iter<'iter> = impl Iterator<Item = Self::Item<'iter>> where Self: 'iter;

    fn slice(self, range: Range<usize>) -> Self
    where
        Self: Sized,
    {
        &self[range]
    }

    fn len(self) -> usize {
        self.chars().count()
    }

    fn items<'a>(self) -> Self::Iter<'a>
    where
        Self: 'a,
    {
        self.chars()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn test_take() {
        let input = &[1, 2, 3, 4, 5];
        assert_eq!(take(1)(input.as_slice()).unwrap().1, &[1])
    }

    #[test]
    fn test_take_while() {
        let input = &[1, 2, 3, 4, 5];

        assert!(matches!(
            take_while(|i: &u64| *i != 3)(input.as_slice()).unwrap(),
            (&[3, 4, 5], &[1, 2])
        ));
    }

    #[test]
    fn test_take_one() {
        let input = &[1, 2, 3, 4, 5];

        assert!(matches!(
            take_one(input.as_slice()).unwrap(),
            (&[2, 3, 4, 5], 1)
        ));
    }

    #[test]
    fn test_separated() {
        let input = &[1, 2, 3, 4, 5];

        assert!(matches!(
            separated(
                take_while(|i: &u64| *i != 3),
                take_one,
                take_while(|_| true)
            )(input.as_slice())
            .unwrap(),
            (_, (&[1, 2], &[4, 5]))
        ));
    }
}
