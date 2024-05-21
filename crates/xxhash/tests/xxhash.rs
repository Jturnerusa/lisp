use std::hash::Hasher;

use xxhash::Xxh3;

#[test]
fn test_input() {
    let input = b"hello world\n";
    let mut hasher = Xxh3::new(0).unwrap();

    hasher.write(input);

    assert_eq!(hasher.finish(), 0xd42f7ed4b73c6bde)
}
