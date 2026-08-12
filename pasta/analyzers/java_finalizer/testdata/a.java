class A {
    @Override // want "Object.finalize is deprecated"
    protected void finalize() throws Throwable {
        super.finalize();
    }

    public void normal() {}

    // Methods named finalize but with parameters are fine — they're
    // not overrides of Object.finalize.
    public void finalize(int x) {}

    // Non-void finalize() is not Object.finalize.
    public int finalize() {
        return 0;
    }

    public void close() {}
}
