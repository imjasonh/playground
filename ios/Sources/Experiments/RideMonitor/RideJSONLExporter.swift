import Foundation
import SwiftUI
import UniformTypeIdentifiers

/// Exports saved rides as JSON Lines: one compact JSON object per line. The
/// first line is ride metadata; following lines are events, GPS fixes, motion
/// summaries, and barometer samples (each tagged with `"type"`).
enum RideJSONLExporter {
    private static let filenameStampFormatter: DateFormatter = {
        let formatter = DateFormatter()
        formatter.locale = Locale(identifier: "en_US_POSIX")
        formatter.timeZone = .current
        formatter.dateFormat = "yyyy-MM-dd'T'HH-mm-ss"
        return formatter
    }()

    private struct RideHeader: Encodable {
        let type = "ride"
        let id: UUID
        let startedAt: Date
        let endedAt: Date
        let durationSeconds: TimeInterval
        let distanceMeters: Double
        let peakG: Double
        let joltCount: Int
        let crashCount: Int
    }

    private struct EventLine: Encodable {
        let type = "event"
        let id: UUID
        let severity: RideSeverity
        let peakG: Double
        let at: TimeInterval
        let latitude: Double?
        let longitude: Double?
    }

    private struct LocationLine: Encodable {
        let type = "location"
        let t: TimeInterval
        let latitude: Double
        let longitude: Double
        let altitude: Double
        let horizontalAccuracy: Double
        let verticalAccuracy: Double
        let speed: Double
        let course: Double
    }

    private struct MotionLine: Encodable {
        let type = "motion"
        let t: TimeInterval
        let peakG: Double
        let meanG: Double
        let peakRotation: Double
        let samples: Int
    }

    private struct BarometerLine: Encodable {
        let type = "barometer"
        let t: TimeInterval
        let relativeAltitude: Double
        let pressureKPa: Double
    }

    static let contentType = UTType(filenameExtension: "jsonl") ?? .json

    /// JSONL bytes for one ride (UTF-8, newline-terminated).
    static func data(for ride: Ride) throws -> Data {
        let lines = try lines(for: ride)
        guard let text = lines.joined(separator: "\n").appending("\n").data(using: .utf8) else {
            throw ExportError.encodingFailed
        }
        return text
    }

    /// JSONL bytes for many rides, concatenated in order (each ride is a block
    /// of lines starting with a `"type":"ride"` header).
    static func data(for rides: [Ride]) throws -> Data {
        var chunks: [Data] = []
        chunks.reserveCapacity(rides.count)
        for ride in rides {
            chunks.append(try data(for: ride))
        }
        return chunks.reduce(into: Data()) { $0.append($1) }
    }

    /// Suggested filename for a single ride export.
    static func filename(for ride: Ride) -> String {
        let stamp = filenameStampFormatter.string(from: ride.startedAt)
        return "ride-\(stamp).jsonl"
    }

    /// Suggested filename when exporting every saved ride.
    static func filenameForAllRides() -> String {
        let stamp = filenameStampFormatter.string(from: Date())
        return "rides-\(stamp).jsonl"
    }

    static func lines(for ride: Ride) throws -> [String] {
        var lines: [String] = []
        lines.reserveCapacity(
            1 + ride.events.count + ride.track.count + ride.motion.count + ride.barometer.count
        )

        lines.append(try encode(RideHeader(
            id: ride.id,
            startedAt: ride.startedAt,
            endedAt: ride.endedAt,
            durationSeconds: ride.durationSeconds,
            distanceMeters: ride.distanceMeters,
            peakG: ride.peakG,
            joltCount: ride.joltCount,
            crashCount: ride.crashCount
        )))

        for event in ride.events {
            lines.append(try encode(EventLine(
                id: event.id,
                severity: event.severity,
                peakG: event.peakG,
                at: event.at,
                latitude: event.latitude,
                longitude: event.longitude
            )))
        }

        for sample in ride.track {
            lines.append(try encode(LocationLine(
                t: sample.t,
                latitude: sample.latitude,
                longitude: sample.longitude,
                altitude: sample.altitude,
                horizontalAccuracy: sample.horizontalAccuracy,
                verticalAccuracy: sample.verticalAccuracy,
                speed: sample.speed,
                course: sample.course
            )))
        }

        for summary in ride.motion {
            lines.append(try encode(MotionLine(
                t: summary.t,
                peakG: summary.peakG,
                meanG: summary.meanG,
                peakRotation: summary.peakRotation,
                samples: summary.samples
            )))
        }

        for sample in ride.barometer {
            lines.append(try encode(BarometerLine(
                t: sample.t,
                relativeAltitude: sample.relativeAltitude,
                pressureKPa: sample.pressureKPa
            )))
        }

        return lines
    }

    private static func encode<T: Encodable>(_ value: T) throws -> String {
        let encoder = JSONEncoder()
        encoder.dateEncodingStrategy = .iso8601
        encoder.outputFormatting = [.sortedKeys]
        let data = try encoder.encode(value)
        guard let line = String(data: data, encoding: .utf8) else {
            throw ExportError.encodingFailed
        }
        return line
    }

    enum ExportError: Error {
        case encodingFailed
    }
}

/// Share-sheet payload for one ride's JSONL export.
struct RideJSONLExport: Transferable {
    let ride: Ride

    static var transferRepresentation: some TransferRepresentation {
        FileRepresentation(exportedContentType: RideJSONLExporter.contentType) { item in
            let url = FileManager.default.temporaryDirectory
                .appendingPathComponent(RideJSONLExporter.filename(for: item.ride))
            let data = try RideJSONLExporter.data(for: item.ride)
            try data.write(to: url, options: .atomic)
            return SentTransferredFile(url)
        }
    }
}

/// Share-sheet payload for every saved ride in one JSONL file.
struct AllRidesJSONLExport: Transferable {
    let rides: [Ride]

    static var transferRepresentation: some TransferRepresentation {
        FileRepresentation(exportedContentType: RideJSONLExporter.contentType) { item in
            let url = FileManager.default.temporaryDirectory
                .appendingPathComponent(RideJSONLExporter.filenameForAllRides())
            let data = try RideJSONLExporter.data(for: item.rides)
            try data.write(to: url, options: .atomic)
            return SentTransferredFile(url)
        }
    }
}
