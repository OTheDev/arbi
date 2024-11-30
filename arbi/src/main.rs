fn main() {
    use arbi::Arbi;

    let a = Arbi::new();
    let b = Arbi::default();
    let c = Arbi::zero();

    assert_eq!(a, 0);
    assert_eq!(a, b);
    assert_eq!(b, c);
}
