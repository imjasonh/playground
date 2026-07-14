import Foundation

/// Strips non-finite doubles (NaN / ±Inf) that would make `JSONEncoder` throw
/// and lose the only in-memory copy of a just-finished ride.
enum RideSampleSanitizer {
    static func sanitize(_ ride: Ride) -> Ride {
        var diagnostics = ride.recordingDiagnostics
        if var next = diagnostics {
            next.lastMotionOffset = finiteOptional(next.lastMotionOffset)
            next.lastLocationOffset = finiteOptional(next.lastLocationOffset)
            next.maxCompanionPushMilliseconds = finiteOptional(next.maxCompanionPushMilliseconds)
            diagnostics = next
        }

        return Ride(
            id: ride.id,
            startedAt: ride.startedAt,
            endedAt: ride.endedAt,
            durationSeconds: finite(ride.durationSeconds, fallback: 0),
            distanceMeters: finite(ride.distanceMeters, fallback: 0),
            peakG: finite(ride.peakG, fallback: 0),
            joltCount: ride.joltCount,
            crashCount: ride.crashCount,
            summary: ride.summary,
            averageHeartRateBPM: finiteOptional(ride.averageHeartRateBPM),
            maxHeartRateBPM: finiteOptional(ride.maxHeartRateBPM),
            activeEnergyKilocalories: finiteOptional(ride.activeEnergyKilocalories),
            basalEnergyKilocalories: finiteOptional(ride.basalEnergyKilocalories),
            watchDistanceMeters: finiteOptional(ride.watchDistanceMeters),
            averageCadenceRPM: finiteOptional(ride.averageCadenceRPM),
            averageCyclingPowerWatts: finiteOptional(ride.averageCyclingPowerWatts),
            maxCyclingPowerWatts: finiteOptional(ride.maxCyclingPowerWatts),
            recordingDiagnostics: diagnostics,
            events: ride.events.map { event in
                RideEvent(
                    id: event.id,
                    severity: event.severity,
                    peakG: finite(event.peakG, fallback: 0),
                    at: finite(event.at, fallback: 0),
                    latitude: finiteOptional(event.latitude),
                    longitude: finiteOptional(event.longitude)
                )
            },
            track: ride.track.map { sample in
                LocationSample(
                    t: finite(sample.t, fallback: 0),
                    latitude: finite(sample.latitude, fallback: 0),
                    longitude: finite(sample.longitude, fallback: 0),
                    altitude: finite(sample.altitude, fallback: 0),
                    horizontalAccuracy: finite(sample.horizontalAccuracy, fallback: -1),
                    verticalAccuracy: finite(sample.verticalAccuracy, fallback: -1),
                    speed: finite(sample.speed, fallback: -1),
                    course: finite(sample.course, fallback: -1)
                )
            },
            motion: ride.motion.map { summary in
                MotionSummary(
                    t: finite(summary.t, fallback: 0),
                    peakG: finite(summary.peakG, fallback: 0),
                    meanG: finite(summary.meanG, fallback: 0),
                    peakRotation: finite(summary.peakRotation, fallback: 0),
                    samples: max(0, summary.samples)
                )
            },
            barometer: ride.barometer.map { sample in
                AltitudeSample(
                    t: finite(sample.t, fallback: 0),
                    relativeAltitude: finite(sample.relativeAltitude, fallback: 0),
                    pressureKPa: finite(sample.pressureKPa, fallback: 0)
                )
            }
        )
    }

    static func finite(_ value: Double, fallback: Double) -> Double {
        value.isFinite ? value : fallback
    }

    static func finiteOptional(_ value: Double?) -> Double? {
        guard let value else { return nil }
        return value.isFinite ? value : nil
    }
}
