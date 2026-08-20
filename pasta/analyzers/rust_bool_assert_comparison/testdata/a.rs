fn f(x: bool) {
    assert_eq!(x, false); // want "asserting equality to a bool literal"
    assert_eq!(false, x); // want "asserting equality to a bool literal"
    assert_eq!(x, true); // want "asserting equality to a bool literal"
    assert_ne!(x, true); // want "asserting equality to a bool literal"
    assert!(x);
    assert_eq!(x, 0);
}
