func load() -> String {
    return try! readFile()   // want "try! will crash"
}

func loadSafe() -> String? {
    return try? readFile()   // OK
}

func loadPropagate() throws -> String {
    return try readFile()    // OK
}
