import Foundation
import SwiftUI

/// Navigates the launcher into experiments from deep links and App Intents.
@MainActor
final class PlaygroundRouter: ObservableObject {
    static let shared = PlaygroundRouter()

    @Published var path: [String] = []

    func openDeviceAgent() {
        if path.last == "device-agent" { return }
        if path.contains("device-agent") {
            path.removeAll { $0 == "device-agent" }
        }
        path.append("device-agent")
    }

    func handleOpenURL(_ url: URL) {
        if AgentInbox.shared.handleOpenURL(url) {
            openDeviceAgent()
        }
    }
}
