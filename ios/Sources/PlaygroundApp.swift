import SwiftUI

/// Entry point for the single "Playground" iOS app. The app itself is just a
/// shell: it shows a launcher (`RootView`) listing every experiment registered
/// in `ExperimentCatalog`. New functional experiments are added there, not as
/// separate apps.
@main
struct PlaygroundApp: App {
    @ObservedObject private var router = PlaygroundRouter.shared

    var body: some Scene {
        WindowGroup {
            RootView()
                .environmentObject(router)
                // Ride Monitor Live Activities can outlive a force-quit. Clear
                // orphans at cold launch so Dynamic Island / Lock Screen don't
                // keep looking like a ride is recording before the user opens
                // the experiment.
                .onAppear {
                    RideLiveActivityController.shared.endOrphansIfNeeded()
                    if AgentInbox.shared.shouldOpenExperiment {
                        router.openDeviceAgent()
                        AgentInbox.shared.shouldOpenExperiment = false
                    }
                }
                .onOpenURL { url in
                    if url.isFileURL {
                        Task { @MainActor in
                            do {
                                _ = try AgentInbox.shared.importFile(from: url)
                                AgentInbox.shared.enqueue(
                                    prompt: "List attachments and summarize any text files.",
                                    source: .share,
                                    mode: .act
                                )
                                router.openDeviceAgent()
                            } catch {
                                // Ignore unreadable opens; deep links still work below.
                            }
                        }
                    }
                    router.handleOpenURL(url)
                }
                .onReceive(AgentInbox.shared.$shouldOpenExperiment) { shouldOpen in
                    if shouldOpen {
                        router.openDeviceAgent()
                        AgentInbox.shared.shouldOpenExperiment = false
                    }
                }
        }
    }
}
