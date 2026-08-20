class A {
    // Overloaded finalize is not Object.finalize and never runs.
    public void finalize(int x) {} // want "finalize(…) with parameters"

    @Override
    protected void finalize() throws Throwable {
        super.finalize();
    }

    public void close() {}

    public int finalize() {
        return 0;
    }
}
