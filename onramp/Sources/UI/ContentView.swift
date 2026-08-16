import SwiftUI

struct ContentView: View {
    @EnvironmentObject private var foundationModelsGate: FoundationModelsGateModel
    @EnvironmentObject private var onboarding: OnboardingModel
    @State private var selectedTab: AppTab = .playbooks

    private enum AppTab: Hashable {
        case playbooks
        case toolbox
        case chat
    }

    var body: some View {
        Group {
            if !foundationModelsGate.showsMainApp {
                FoundationModelsGateView(gate: foundationModelsGate)
            } else if onboarding.showReadyFlow, foundationModelsGate.status == .available {
                FirstRunReadyView(onboarding: onboarding) {
                    selectedTab = .playbooks
                }
            } else {
                mainTabs
            }
        }
        .frame(minWidth: 800, minHeight: 540)
        .onAppear {
            foundationModelsGate.refresh()
        }
        .onChange(of: foundationModelsGate.status) { _, status in
            if status == .available, !onboarding.isCompleted {
                onboarding.showReadyFlow = true
            }
        }
    }

    private var mainTabs: some View {
        TabView(selection: $selectedTab) {
            PlaybooksView(autoStartCantGetOnline: true)
                .tabItem {
                    Label("Playbooks", systemImage: "list.bullet.clipboard")
                }
                .tag(AppTab.playbooks)
                .accessibilityIdentifier("tab-playbooks")

            ManualToolboxView()
                .tabItem {
                    Label("Toolbox", systemImage: "wrench.and.screwdriver")
                }
                .tag(AppTab.toolbox)
                .accessibilityIdentifier("tab-toolbox")

            NavigationStack {
                ChatView()
            }
            .tabItem {
                Label("Chat", systemImage: "bubble.left.and.bubble.right")
            }
            .tag(AppTab.chat)
            .accessibilityIdentifier("tab-chat")
        }
    }
}

#Preview {
    ContentView()
        .environmentObject(FoundationModelsGateModel())
        .environmentObject(OnboardingModel())
}
