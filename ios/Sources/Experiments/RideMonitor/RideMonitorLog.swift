import Foundation
import OSLog

/// Structured Console logs for Ride Monitor recording. Filter in Console.app /
/// Xcode with subsystem `io.github.imjasonh.playground` and category
/// `RideMonitor`. Messages stay public so device logs remain readable when
/// attached via Cable / wireless debugging after a mid-ride stop.
enum RideMonitorLog {
    static let logger = Logger(
        subsystem: "io.github.imjasonh.playground",
        category: "RideMonitor"
    )

    static func info(_ message: String) {
        logger.info("\(message, privacy: .public)")
    }

    static func notice(_ message: String) {
        logger.notice("\(message, privacy: .public)")
    }

    static func error(_ message: String) {
        logger.error("\(message, privacy: .public)")
    }

    static func fault(_ message: String) {
        logger.fault("\(message, privacy: .public)")
    }
}
