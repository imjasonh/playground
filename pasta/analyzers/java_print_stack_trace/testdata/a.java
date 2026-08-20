class A {
    void fail(Exception e) {
        e.printStackTrace(); // want "printStackTrace dumps to stderr"
        e.printStackTrace(System.out); // want "printStackTrace dumps to stderr"
    }

    void ok(java.util.logging.Logger log, Exception e) {
        log.log(java.util.logging.Level.SEVERE, "failed", e);
    }
}
