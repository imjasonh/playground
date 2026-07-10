import SwiftUI

/// Follow the Hum — a nearby spot is hidden; a spatial hum in your AirPods
/// steers you until you find it. The phone screen is secondary: listen and walk.
struct FollowTheHumView: View {
    @StateObject private var session = HumHuntSession()

    var body: some View {
        ScrollView {
            VStack(spacing: 24) {
                hero
                compassHint
                controls
                Text(session.statusMessage)
                    .font(.body)
                    .multilineTextAlignment(.center)
                    .foregroundStyle(.secondary)
                    .accessibilityIdentifier("humStatusMessage")

                if session.phase == .hunting, let distance = session.distanceMeters {
                    Text(warmthLabel(distance))
                        .font(.title3.weight(.semibold))
                        .accessibilityIdentifier("humDistance")
                }

                tips
                disclaimer
            }
            .padding()
        }
        .background(atmosphere.ignoresSafeArea())
    }

    private var hero: some View {
        VStack(spacing: 8) {
            Image(systemName: session.isFound ? "checkmark.seal.fill" : "waveform.circle.fill")
                .font(.system(size: 64))
                .foregroundStyle(session.isFound ? Color.green : Color.accentColor)
                .accessibilityHidden(true)

            Text(session.isFound ? "Found" : session.isHunting ? "Listening…" : "Follow the Hum")
                .font(.largeTitle.weight(.bold))
                .accessibilityIdentifier("humTitle")

            Text("A soft hum hides a walkable spot nearby. Turn until it sits in front of you, then walk toward it.")
                .font(.subheadline)
                .foregroundStyle(.secondary)
                .multilineTextAlignment(.center)
        }
    }

    private var compassHint: some View {
        Group {
            if session.isHunting, let relative = session.relativeBearingDegrees {
                VStack(spacing: 6) {
                    Text(steeringLabel(relative))
                        .font(.headline)
                    GeometryReader { geo in
                        let width = geo.size.width
                        let x = width / 2 + CGFloat(sin(relative * .pi / 180)) * (width / 2 - 16)
                        Circle()
                            .fill(Color.accentColor)
                            .frame(width: 18, height: 18)
                            .position(x: x, y: 12)
                            .animation(.easeOut(duration: 0.15), value: relative)
                    }
                    .frame(height: 24)
                    .accessibilityIdentifier("humPanIndicator")
                }
                .padding()
                .frame(maxWidth: .infinity)
                .background(.ultraThinMaterial, in: RoundedRectangle(cornerRadius: 16))
            }
        }
    }

    private var controls: some View {
        Group {
            if session.isHunting {
                Button(role: .destructive) {
                    session.stop()
                } label: {
                    Label("Stop hunt", systemImage: "stop.circle.fill")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.borderedProminent)
                .accessibilityIdentifier("stopHumHuntButton")
            } else {
                Button {
                    session.requestPermissionsAndStart()
                } label: {
                    Label(session.isFound ? "Hunt again" : "Start hunt", systemImage: "headphones")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.borderedProminent)
                .accessibilityIdentifier("startHumHuntButton")
            }
        }
    }

    private var tips: some View {
        VStack(alignment: .leading, spacing: 8) {
            Label("AirPods in ears — the hum follows your head, not the phone", systemImage: "headphones")
            Label("At start, hold the phone facing the way you're looking (locks north)", systemImage: "location.north.line")
            Label("Then pocket the phone; turn until the hum is centered and walk", systemImage: "ear")
            Label("It brightens and clears as you get closer", systemImage: "sparkles")
        }
        .font(.footnote)
        .foregroundStyle(.secondary)
        .frame(maxWidth: .infinity, alignment: .leading)
    }

    private var disclaimer: some View {
        Text("Walk somewhere safe and look up from the screen. This is a playful experiment — not a navigation or safety tool. Stay aware of traffic and surroundings.")
            .font(.caption2)
            .foregroundStyle(.tertiary)
            .multilineTextAlignment(.leading)
    }

    private var atmosphere: some View {
        LinearGradient(
            colors: [
                Color(red: 0.93, green: 0.96, blue: 0.94),
                Color(red: 0.86, green: 0.91, blue: 0.95),
            ],
            startPoint: .topLeading,
            endPoint: .bottomTrailing
        )
    }

    private func warmthLabel(_ meters: Double) -> String {
        switch meters {
        case ..<40: return "Burning warm"
        case ..<90: return "Warm"
        case ..<160: return "Mild"
        case ..<240: return "Cool"
        default: return "Distant chill"
        }
    }

    private func steeringLabel(_ relative: Double) -> String {
        let absRel = abs(relative)
        if absRel < 20 { return "Hum ahead" }
        if relative > 0 { return "Hum to your right" }
        return "Hum to your left"
    }
}

#Preview {
    NavigationStack {
        FollowTheHumView()
            .navigationTitle("Follow the Hum")
    }
}
