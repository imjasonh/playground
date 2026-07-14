import SwiftUI

@main
struct RideMonitorWatchApp: App {
    @WKApplicationDelegateAdaptor(RideWatchAppDelegate.self) private var appDelegate
    @StateObject private var receiver = RideWatchReceiver.shared
    @StateObject private var workout = RideWatchWorkoutController.shared

    var body: some Scene {
        WindowGroup {
            RideMonitorWatchView()
                .environmentObject(receiver)
                .environmentObject(workout)
        }
    }
}
