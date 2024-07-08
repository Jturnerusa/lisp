use std::{
    collections::HashMap,
    hash::{BuildHasher, Hasher},
};

pub type IdentityMap<K, V> = HashMap<K, V, IdentityHasher>;

pub struct IdentityHasher(u64);

#[allow(clippy::new_without_default)]
impl IdentityHasher {
    pub fn new() -> Self {
        Self(0)
    }
}

impl BuildHasher for IdentityHasher {
    type Hasher = IdentityHasher;
    fn build_hasher(&self) -> Self::Hasher {
        Self::new()
    }
}

impl Hasher for IdentityHasher {
    fn write(&mut self, bytes: &[u8]) {
        let mut array = [0u8; 8];

        for (i, byte) in bytes.iter().enumerate() {
            array[i] = *byte;
        }

        self.0 = u64::from_le_bytes(array);
    }

    fn finish(&self) -> u64 {
        self.0
    }
}
