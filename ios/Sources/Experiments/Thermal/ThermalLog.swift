import Foundation
import OSLog

/// Console logs for thermal Live Activity start and failure. Filter in
/// Console.app with subsystem `io.github.imjasonh.playground` and category
/// `Thermal`.
enum ThermalLog {
    static let logger = Logger(
        subsystem: "io.github.imjasonh.playground",
        category: "Thermal"
    )

    static func error(_ message: String) {
        logger.error("\(message, privacy: .public)")
    }
}
