import SwiftUI

@main
struct OnrampApp: App {
    @StateObject private var updater = SparkleUpdater()
    @StateObject private var foundationModelsGate = FoundationModelsGateModel()
    @StateObject private var onboarding = OnboardingModel()

    var body: some Scene {
        WindowGroup {
            ContentView()
                .environmentObject(foundationModelsGate)
                .environmentObject(onboarding)
        }
        .defaultSize(width: 920, height: 660)
        .commands {
            CommandGroup(after: .appInfo) {
                Button("Check for Updates…") {
                    updater.checkForUpdates()
                }
                Button("Check Apple Intelligence…") {
                    foundationModelsGate.allowPlaybooksWithoutModel = false
                    foundationModelsGate.refresh()
                }
                Button("Show first-run setup again…") {
                    UserDefaults.standard.set(false, forKey: "onramp.onboardingCompleted.v1")
                    onboarding.showReadyFlow = true
                }
            }
        }

        MenuBarExtra("Onramp", systemImage: "stethoscope") {
            MenuBarQuickPanel()
                .environmentObject(foundationModelsGate)
        }
        .menuBarExtraStyle(.window)
    }
}
