import SwiftUI

/// Follow the Hum — a nearby spot is hidden; a spatial hum in your AirPods
/// steers you until you find it. The phone screen is secondary: listen and walk.
struct FollowTheHumView: View {
    @Environment(\.colorScheme) private var colorScheme
    @ScaledMetric(relativeTo: .largeTitle) private var heroSymbolSize: CGFloat = 56
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
        VStack(spacing: 12) {
            Image(systemName: session.isFound ? "checkmark.seal.fill" : "waveform.circle.fill")
                .font(.system(size: heroSymbolSize, weight: .regular))
                .symbolRenderingMode(.hierarchical)
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
        .padding(.top, 8)
    }

    private var compassHint: some View {
        Group {
            if session.isHunting, let relative = session.relativeBearingDegrees {
                VStack(spacing: 10) {
                    Text(steeringLabel(relative))
                        .font(.headline)
                    GeometryReader { geo in
                        let width = geo.size.width
                        let x = width / 2 + CGFloat(sin(relative * .pi / 180)) * (width / 2 - 16)
                        ZStack {
                            Capsule()
                                .fill(Color.primary.opacity(0.08))
                                .frame(height: 6)
                                .position(x: width / 2, y: 12)
                            Circle()
                                .fill(Color.accentColor)
                                .frame(width: 18, height: 18)
                                .shadow(color: Color.accentColor.opacity(0.35), radius: 4, y: 1)
                                .position(x: x, y: 12)
                                .animation(.easeOut(duration: 0.15), value: relative)
                        }
                    }
                    .frame(height: 24)
                    .accessibilityElement()
                    .accessibilityLabel(steeringLabel(relative))
                    .accessibilityValue("\(Int(relative.rounded())) degrees")
                    .accessibilityIdentifier("humPanIndicator")
                }
                .padding()
                .frame(maxWidth: .infinity)
                .background(.regularMaterial, in: RoundedRectangle(cornerRadius: 16, style: .continuous))
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
                .controlSize(.large)
                .accessibilityIdentifier("stopHumHuntButton")
            } else {
                Button {
                    session.requestPermissionsAndStart()
                } label: {
                    Label(session.isFound ? "Hunt again" : "Start hunt", systemImage: "headphones")
                        .frame(maxWidth: .infinity)
                }
                .buttonStyle(.borderedProminent)
                .controlSize(.large)
                .accessibilityIdentifier("startHumHuntButton")
            }
        }
    }

    private var tips: some View {
        VStack(alignment: .leading, spacing: 10) {
            tipRow("headphones", "AirPods in ears — the hum follows your head, not the phone")
            tipRow("location.north.line", "At start, hold the phone facing the way you're looking (locks north)")
            tipRow("ear", "Then pocket the phone; turn until the hum is centered and walk")
            tipRow("sparkles", "It brightens and clears as you get closer")
        }
        .padding(14)
        .frame(maxWidth: .infinity, alignment: .leading)
        .background(.thinMaterial, in: RoundedRectangle(cornerRadius: 14, style: .continuous))
    }

    private func tipRow(_ symbol: String, _ text: String) -> some View {
        Label(text, systemImage: symbol)
            .font(.footnote)
            .foregroundStyle(.secondary)
            .labelStyle(.titleAndIcon)
    }

    private var disclaimer: some View {
        Text("Walk somewhere safe and look up from the screen. This is a playful experiment — not a navigation or safety tool. Stay aware of traffic and surroundings.")
            .font(.caption2)
            .foregroundStyle(.tertiary)
            .multilineTextAlignment(.leading)
    }

    /// Soft teal wash that tracks Light/Dark Mode instead of a fixed cream gradient.
    private var atmosphere: some View {
        let deep = colorScheme == .dark
        return LinearGradient(
            colors: [
                Color(uiColor: .systemBackground),
                Color.accentColor.opacity(deep ? 0.18 : 0.10),
                Color.teal.opacity(deep ? 0.12 : 0.08),
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
