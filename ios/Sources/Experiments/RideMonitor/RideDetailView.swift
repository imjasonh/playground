import SwiftUI
import Charts

/// Detail view for one saved ride: summary stats, the same elevation/speed
/// sparkline used by the Live Activity, a g-force-over-time chart, and a
/// speed-colored route map (capped to the biggest event pins). Events stay
/// recorded in the ride file; the map's top-N pins surface the big ones.
struct RideDetailView: View {
    let ride: Ride

    /// In-app can afford a denser sparkline than ActivityKit's 48-point budget.
    private var elevationProfile: [RideProfilePoint] {
        RideProfileBuilder.build(
            altitudes: ride.barometer,
            track: ride.track,
            maxPoints: 96
        )
    }

    var body: some View {
        List {
            Section("Summary") {
                if let summary = ride.summary, !summary.isEmpty {
                    Text(summary)
                        .font(.body)
                        .accessibilityIdentifier("rideDetailSummary")
                }
                stat("Started", ride.startedAt.formatted(date: .abbreviated, time: .shortened))
                stat("Duration", duration(ride.durationSeconds))
                stat("Distance", String(format: "%.2f mi", RideUnits.miles(fromMeters: ride.distanceMeters)))
                stat("Max speed", String(format: "%.1f mph", RideUnits.milesPerHour(fromMetersPerSecond: ride.maxSpeed)))
                stat("Peak g", String(format: "%.1f g", ride.peakG))
                stat("Jolts", "\(ride.joltCount)")
                stat("Possible crashes", "\(ride.crashCount)")
                if let bpm = ride.averageHeartRateBPM {
                    stat("Avg heart rate", String(format: "%.0f bpm", bpm))
                }
                if let bpm = ride.maxHeartRateBPM {
                    stat("Max heart rate", String(format: "%.0f bpm", bpm))
                }
                if let kcal = ride.activeEnergyKilocalories {
                    stat("Active energy", String(format: "%.0f kcal", kcal))
                }
                if let kcal = ride.basalEnergyKilocalories {
                    stat("Basal energy", String(format: "%.0f kcal", kcal))
                }
                if let meters = ride.watchDistanceMeters {
                    stat("Watch distance", String(format: "%.2f mi", RideUnits.miles(fromMeters: meters)))
                }
                if let rpm = ride.averageCadenceRPM {
                    stat("Avg cadence", String(format: "%.0f rpm", rpm))
                }
                if let watts = ride.averageCyclingPowerWatts {
                    stat("Avg power", String(format: "%.0f W", watts))
                }
                if let watts = ride.maxCyclingPowerWatts {
                    stat("Max power", String(format: "%.0f W", watts))
                }
                if let gain = ride.elevationGain {
                    stat("Net elevation", String(format: "%+.1f m", gain))
                }
            }

            if elevationProfile.count >= 2 {
                Section("Elevation & speed") {
                    VStack(alignment: .leading, spacing: 8) {
                        RideElevationProfileView(points: elevationProfile)
                            .frame(height: 88)
                            .accessibilityIdentifier("rideDetailElevationProfile")
                        speedLegend
                    }
                    .padding(.vertical, 4)
                }
            }

            if hasCoordinates {
                Section("Route") {
                    RideMapView(track: ride.track, events: ride.events)
                        .frame(height: 260)
                        .listRowInsets(EdgeInsets())
                    speedLegend
                        .padding(.vertical, 4)
                    if mappableEventCount > RideMapEventFilter.defaultLimit {
                        Text("Showing the \(RideMapEventFilter.defaultLimit) biggest events on the map. All \(ride.events.count) remain in the ride file.")
                            .font(.caption)
                            .foregroundStyle(.secondary)
                    }
                }
            }

            if !ride.motion.isEmpty {
                Section("Acceleration over time") {
                    Chart {
                        ForEach(ride.motion, id: \.t) { sample in
                            LineMark(
                                x: .value("Time (s)", sample.t),
                                y: .value("Peak g", sample.peakG)
                            )
                        }
                    }
                    .frame(height: 160)
                }
            }

            if let diagnostics = ride.recordingDiagnostics {
                Section("Recording end") {
                    stat("Reason", diagnostics.endReason.displayName)
                    if let detail = diagnostics.endDetail, !detail.isEmpty {
                        Text(detail)
                            .font(.caption)
                            .foregroundStyle(.secondary)
                            .accessibilityIdentifier("rideDetailEndDetail")
                    }
                    if let offset = diagnostics.lastMotionOffset {
                        stat("Last motion", duration(offset))
                    }
                    if let offset = diagnostics.lastLocationOffset {
                        stat("Last GPS", duration(offset))
                    }
                    stat("Motion restarts", "\(diagnostics.motionRestartCount)")
                    stat("Location errors", "\(diagnostics.locationErrorCount)")
                    if let pushMs = diagnostics.maxCompanionPushMilliseconds {
                        stat("Slowest companion push", String(format: "%.0f ms", pushMs))
                    }
                    if let auth = diagnostics.authorizationStatusAtEnd {
                        stat("Location at end", auth)
                    }
                }
            }

            Section("Sensor log") {
                stat("GPS fixes", "\(ride.track.count)")
                stat("Motion seconds", "\(ride.motion.count)")
                stat("Barometer samples", "\(ride.barometer.count)")
                if let first = ride.track.first {
                    stat("Start", String(format: "%.5f, %.5f", first.latitude, first.longitude))
                }
                if let last = ride.track.last {
                    stat("End", String(format: "%.5f, %.5f", last.latitude, last.longitude))
                }
            }
        }
        .navigationTitle("Ride")
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .topBarTrailing) {
                ShareLink(
                    item: RideJSONLExport(ride: ride),
                    preview: SharePreview("Ride JSONL", image: Image(systemName: "doc.text"))
                ) {
                    Label("Export JSONL", systemImage: "square.and.arrow.up")
                }
                .accessibilityIdentifier("exportRideJSONLButton")
            }
        }
    }

    private var hasCoordinates: Bool {
        !ride.track.isEmpty || ride.events.contains { $0.latitude != nil && $0.longitude != nil }
    }

    private var mappableEventCount: Int {
        ride.events.filter { $0.latitude != nil && $0.longitude != nil }.count
    }

    private var speedLegend: some View {
        HStack(spacing: 10) {
            legendDot(.blue, "slow")
            legendDot(.green, "easy")
            legendDot(.orange, "brisk")
            legendDot(.red, "fast")
            Spacer()
        }
        .font(.caption2)
        .foregroundStyle(.secondary)
    }

    private func stat(_ label: String, _ value: String) -> some View {
        HStack {
            Text(label)
            Spacer()
            Text(value).foregroundStyle(.secondary).monospacedDigit()
        }
    }

    private func legendDot(_ color: Color, _ label: String) -> some View {
        HStack(spacing: 4) {
            Circle().fill(color).frame(width: 6, height: 6)
            Text(label)
        }
    }

    private func duration(_ seconds: TimeInterval) -> String {
        let total = Int(seconds)
        return String(format: "%d:%02d", total / 60, total % 60)
    }
}
