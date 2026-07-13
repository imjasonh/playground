import SwiftUI

@main
struct RideMonitorWatchApp: App {
    @StateObject private var receiver = RideWatchReceiver.shared

    var body: some Scene {
        WindowGroup {
            RideMonitorWatchView()
                .environmentObject(receiver)
        }
    }
}
