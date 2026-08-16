import Foundation

/// Runs argv-style CLI helpers with a timeout. Prefer frameworks; use this only
/// as a fallback when SystemConfiguration / Network are insufficient.
enum ProcessRunner {
    struct Result: Equatable, Sendable {
        var exitCode: Int32
        var stdout: String
        var stderr: String
        var timedOut: Bool
    }

    static func run(
        _ executable: String,
        arguments: [String],
        timeoutSeconds: TimeInterval = 8,
        maxOutputBytes: Int = 64_000
    ) throws -> Result {
        let process = Process()
        process.executableURL = URL(fileURLWithPath: executable)
        process.arguments = arguments

        let outPipe = Pipe()
        let errPipe = Pipe()
        process.standardOutput = outPipe
        process.standardError = errPipe

        try process.run()

        let group = DispatchGroup()
        group.enter()
        DispatchQueue.global(qos: .userInitiated).async {
            process.waitUntilExit()
            group.leave()
        }

        let waitResult = group.wait(timeout: .now() + timeoutSeconds)
        if waitResult == .timedOut {
            process.terminate()
            _ = group.wait(timeout: .now() + 2)
            return Result(
                exitCode: -1,
                stdout: truncate(readPipe(outPipe), maxOutputBytes),
                stderr: truncate(readPipe(errPipe), maxOutputBytes),
                timedOut: true
            )
        }

        return Result(
            exitCode: process.terminationStatus,
            stdout: truncate(readPipe(outPipe), maxOutputBytes),
            stderr: truncate(readPipe(errPipe), maxOutputBytes),
            timedOut: false
        )
    }

    private static func readPipe(_ pipe: Pipe) -> String {
        let data = pipe.fileHandleForReading.readDataToEndOfFile()
        return String(data: data, encoding: .utf8) ?? ""
    }

    private static func truncate(_ text: String, _ maxBytes: Int) -> String {
        guard text.utf8.count > maxBytes else { return text }
        let end = text.utf8.index(text.utf8.startIndex, offsetBy: maxBytes)
        return String(text[..<end]) + "\n…(truncated)"
    }
}
