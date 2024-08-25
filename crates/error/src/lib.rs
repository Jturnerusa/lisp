use core::fmt;

pub trait Error: fmt::Debug {
    fn span(&self) -> Option<FileSpan>;
    fn message(&self, writer: &mut dyn std::io::Write);
}

#[derive(Clone, Copy, Debug, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct FileSpan {
    pub id: u64,
    pub start: usize,
    pub stop: usize,
}

impl<T: Error + 'static> From<T> for Box<dyn Error> {
    fn from(value: T) -> Self {
        Box::new(value)
    }
}

impl<T: std::error::Error> Error for T {
    fn span(&self) -> Option<FileSpan> {
        None
    }

    fn message(&self, writer: &mut dyn std::io::Write) {
        write!(writer, "{self}").unwrap();
    }
}
