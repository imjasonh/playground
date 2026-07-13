import SwiftUI

/// Background-capable ride monitor that flags shakes, potholes, hard impacts,
/// and possible crashes from the accelerometer while you bike, logging where
/// each happened.
struct RideMonitorView: View {
    @StateObject private var monitor = RideMonitor()

    var body: some View {
        ScrollView {
            VStack(spacing: 20) {
                gauge
                stats

                if monitor.isRunning {
                    Button(role: .destructive) {
                        monitor.stop()
                    } label: {
                        Label("Stop ride", systemImage: "stop.circle.fill")
                            .frame(maxWidth: .infinity)
                    }
                    .buttonStyle(.borderedProminent)
                    .accessibilityIdentifier("stopRideButton")
                } else {
                    Button {
                        monitor.start()
                    } label: {
                        Label("Start ride", systemImage: "bicycle")
                            .frame(maxWidth: .infinity)
                    }
                    .buttonStyle(.borderedProminent)
                    .accessibilityIdentifier("startRideButton")
                }

                Text(monitor.statusMessage)
                    .font(.footnote)
                    .foregroundStyle(.secondary)

                NavigationLink {
                    RideListView()
                } label: {
                    Label("Past rides", systemImage: "list.bullet.rectangle")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.bordered)
                .accessibilityIdentifier("pastRidesButton")

                eventLog

                disclaimer
            }
            .padding()
        }
        .alert("Possible crash detected", isPresented: Binding(
            get: { monitor.crashAlert },
            set: { if !$0 { monitor.dismissCrashAlert() } }
        )) {
            Button("I'm OK", role: .cancel) { monitor.dismissCrashAlert() }
        } message: {
            Text("A hard impact was followed by stillness. If you're fine, dismiss this.")
        }
    }

    private var gauge: some View {
        VStack(spacing: 4) {
            Text(String(format: "%.2f g", monitor.currentG))
                .font(.system(size: 56, weight: .bold, design: .rounded))
                .monospacedDigit()
                .foregroundStyle(monitor.currentG >= 3 ? .red : monitor.currentG >= 1.2 ? .orange : .primary)
                .accessibilityIdentifier("currentG")
            Text("current acceleration")
                .font(.caption)
                .foregroundStyle(.secondary)
        }
    }

    private var stats: some View {
        HStack {
            stat("Peak", String(format: "%.1f g", monitor.peakG))
            Divider()
            stat("Jolts", "\(monitor.joltCount)")
            Divider()
            stat("Time", format(monitor.elapsed))
            Divider()
            stat("Dist", String(format: "%.2f km", monitor.distanceMeters / 1000))
        }
        .frame(maxWidth: .infinity)
        .fixedSize(horizontal: false, vertical: true)
    }

    private func stat(_ label: String, _ value: String) -> some View {
        VStack {
            Text(value).font(.headline).monospacedDigit()
            Text(label).font(.caption2).foregroundStyle(.secondary)
        }
        .frame(maxWidth: .infinity)
    }

    private var eventLog: some View {
        VStack(alignment: .leading, spacing: 8) {
            if monitor.events.isEmpty {
                Text("No events yet.")
                    .font(.footnote)
                    .foregroundStyle(.secondary)
            } else {
                ForEach(monitor.events) { event in
                    HStack {
                        Image(systemName: event.severity.icon)
                            .foregroundStyle(color(for: event.severity))
                            .frame(width: 28)
                        VStack(alignment: .leading) {
                            Text(event.severity.title).font(.subheadline).bold()
                            Text(location(for: event)).font(.caption2).foregroundStyle(.secondary)
                        }
                        Spacer()
                        VStack(alignment: .trailing) {
                            Text(String(format: "%.1f g", event.peakG)).monospacedDigit()
                            Text(format(event.at)).font(.caption2).foregroundStyle(.secondary)
                        }
                    }
                    .padding(.vertical, 2)
                }
            }
        }
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    private var disclaimer: some View {
        Text("Uses motion + location and keeps recording in the background while a ride is active. Grant “Always” location when asked so accelerometer logging continues with the screen off. This is a toy detector, not a safety or emergency service — don't rely on it in a real crash.")
            .font(.caption2)
            .foregroundStyle(.secondary)
            .multilineTextAlignment(.center)
    }

    private func color(for severity: RideSeverity) -> Color {
        switch severity {
        case .shake: return .blue
        case .pothole: return .orange
        case .impact: return .red
        case .crash: return .pink
        }
    }

    private func location(for event: RideEvent) -> String {
        guard let lat = event.latitude, let lon = event.longitude else { return "no GPS fix" }
        return String(format: "%.5f, %.5f", lat, lon)
    }

    private func format(_ interval: TimeInterval) -> String {
        let total = Int(interval)
        return String(format: "%d:%02d", total / 60, total % 60)
    }
}

#Preview {
    NavigationStack {
        RideMonitorView()
            .navigationTitle("Ride Monitor")
    }
}
