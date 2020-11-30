use reword::BufferBounded;

#[test]
fn do_nothing() {
}

#[test]
fn check_buffer_size() {
    let v: Vec<u8> = vec![0; 3];
    assert_eq!(v.get_buffer_bound(4), 3); 
}

