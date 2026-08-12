class A {
    void debug(String msg) {
        System.out.println(msg); // want "use a logger instead of System.out/err"
        System.err.print(msg);   // want "use a logger instead of System.out/err"
        System.out.printf("%s%n", msg); // want "use a logger instead of System.out/err"
    }

    void ok(java.util.logging.Logger log, String msg) {
        log.info(msg);
    }
}
