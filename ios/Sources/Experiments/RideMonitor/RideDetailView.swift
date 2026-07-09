import SwiftUI
import Charts

/// Detail view for one saved ride: summary stats, a g-force-over-time chart from
/// the per-second motion log, the event list, and a track/elevation summary.
struct RideDetailView: View {
    let ride: Ride

    var body: some View {
        List {
            Section("Summary") {
                stat("Started", ride.startedAt.formatted(date: .abbreviated, time: .shortened))
                stat("Duration", duration(ride.durationSeconds))
                stat("Distance", String(format: "%.2f km", ride.distanceMeters / 1000))
                stat("Max speed", String(format: "%.1f km/h", ride.maxSpeed * 3.6))
                stat("Peak g", String(format: "%.1f g", ride.peakG))
                stat("Jolts", "\(ride.joltCount)")
                stat("Possible crashes", "\(ride.crashCount)")
                if let gain = ride.elevationGain {
                    stat("Net elevation", String(format: "%+.1f m", gain))
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

            Section("Events (\(ride.events.count))") {
                if ride.events.isEmpty {
                    Text("No jolts detected.").font(.footnote).foregroundStyle(.secondary)
                } else {
                    ForEach(ride.events) { event in
                        HStack {
                            Image(systemName: event.severity.icon)
                                .foregroundStyle(color(for: event.severity))
                                .frame(width: 26)
                            Text(event.severity.title)
                            Spacer()
                            Text(String(format: "%.1f g", event.peakG)).monospacedDigit()
                            Text(clock(event.at)).font(.caption2).foregroundStyle(.secondary)
                        }
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
    }

    private func stat(_ label: String, _ value: String) -> some View {
        HStack {
            Text(label)
            Spacer()
            Text(value).foregroundStyle(.secondary).monospacedDigit()
        }
    }

    private func color(for severity: RideSeverity) -> Color {
        switch severity {
        case .shake: return .blue
        case .pothole: return .orange
        case .impact: return .red
        case .crash: return .pink
        }
    }

    private func duration(_ seconds: TimeInterval) -> String {
        let total = Int(seconds)
        return String(format: "%d:%02d", total / 60, total % 60)
    }

    private func clock(_ seconds: TimeInterval) -> String {
        let total = Int(seconds)
        return String(format: "%d:%02d", total / 60, total % 60)
    }
}
