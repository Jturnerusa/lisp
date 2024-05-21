use std::hash::{BuildHasher, Hasher};

use xxhash_sys::XXH3_state_t;

#[derive(Clone, Copy, Debug)]
pub struct Error;

#[derive(Clone, Copy, Debug)]
pub struct Xxh3 {
    state: *mut XXH3_state_t,
}

impl Xxh3 {
    pub fn new(seed: u64) -> Result<Self, Error> {
        unsafe {
            let state = xxhash_sys::XXH3_createState();

            if state.is_null() {
                return Err(Error);
            }

            if xxhash_sys::XXH3_64bits_reset_withSeed(state, seed)
                == xxhash_sys::XXH_errorcode_XXH_ERROR
            {
                return Err(Error);
            }

            Ok(Self { state })
        }
    }
}

impl BuildHasher for Xxh3 {
    type Hasher = Xxh3;
    fn build_hasher(&self) -> Self::Hasher {
        Self::new(0).unwrap()
    }
}

impl Hasher for Xxh3 {
    fn write(&mut self, bytes: &[u8]) {
        unsafe {
            if xxhash_sys::XXH3_64bits_update(self.state, bytes.as_ptr().cast(), bytes.len())
                == xxhash_sys::XXH_errorcode_XXH_ERROR
            {
                panic!()
            }
        }
    }
    fn finish(&self) -> u64 {
        unsafe { xxhash_sys::XXH3_64bits_digest(self.state) }
    }
}
