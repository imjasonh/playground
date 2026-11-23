import SwiftGodot
import SwiftGodotKit
import SwiftUI

/// Holds the single GodotApp runtime for One Tap Quest across navigation visits.
@MainActor
private final class OneTapQuestHost {
    static let shared = OneTapQuestHost()

    let app = GodotApp(packFile: "one-tap-quest.pck")

    private init() {}
}

@MainActor
@Observable
private final class OneTapQuestSession {
    private(set) var isReady = false
    private(set) var level = 1
    private(set) var score = 0
    @ObservationIgnored private var mainNode: Node?
    @ObservationIgnored private var stateConnection: Callable?

    func connect(to handle: GodotAppViewHandle) {
        guard mainNode == nil,
              let scene = handle.getRoot()?.findChild(pattern: "Main", recursive: true, owned: false)
        else {
            return
        }

        let callback = Callable { [weak self] (lv: Int64, _ exp: Int64, score: Int64, _ status: String) in
            DispatchQueue.main.async { [weak self] in
                self?.level = Int(lv)
                self?.score = Int(score)
            }
        }
        guard scene.connect(signal: "state_changed", callable: callback) == .ok else {
            return
        }
        mainNode = scene
        stateConnection = callback
        isReady = true
    }

    func restart(in app: GodotApp) {
        app.runOnGodotThread { [weak self] in
            guard let mainNode = self?.mainNode else { return }
            _ = mainNode.call(method: "new_game")
        }
    }

    func disconnect(in app: GodotApp) {
        isReady = false
        guard let mainNode, let stateConnection else { return }
        app.runOnGodotThread {
            mainNode.disconnect(signal: "state_changed", callable: stateConnection)
        }
        self.mainNode = nil
        self.stateConnection = nil
    }
}

struct OneTapQuestView: View {
    private let host = OneTapQuestHost.shared
    @State private var session = OneTapQuestSession()

    var body: some View {
        ZStack {
            Color(red: 0.05, green: 0.05, blue: 0.08)
                .ignoresSafeArea()

            VStack(spacing: 0) {
                GodotAppView(onReady: { handle in
                    Task { @MainActor in
                        session.connect(to: handle)
                    }
                })
                .aspectRatio(250.0 / 300.0, contentMode: .fit)
                .frame(maxWidth: .infinity, maxHeight: .infinity)
                .accessibilityIdentifier("one-tap-quest-canvas")

                if let originalURL = URL(string: "http://shimage.net/one-tap-quest/") {
                    Link(destination: originalURL) {
                        Text("Unofficial AI-built recreation of One Tap Quest by shimage.net")
                            .font(.caption)
                            .foregroundStyle(.secondary)
                            .underline()
                            .multilineTextAlignment(.center)
                            .padding(.horizontal, 12)
                            .padding(.vertical, 8)
                    }
                    .accessibilityIdentifier("one-tap-quest-attribution")
                }
            }
        }
        .environment(\.godotApp, host.app)
        .navigationTitle("One Tap Quest")
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .topBarTrailing) {
                Button("Restart") {
                    session.restart(in: host.app)
                }
                .disabled(!session.isReady)
                .accessibilityIdentifier("one-tap-quest-restart")
            }
        }
        .onAppear {
            host.app.resume()
            host.app.startDrawing()
        }
        .onDisappear {
            session.disconnect(in: host.app)
            host.app.pause()
            host.app.stopDrawing()
        }
    }
}
