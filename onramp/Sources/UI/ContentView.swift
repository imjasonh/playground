import SwiftUI

struct ContentView: View {
    @EnvironmentObject private var foundationModelsGate: FoundationModelsGateModel

    var body: some View {
        Group {
            if foundationModelsGate.showsMainApp {
                mainTabs
            } else {
                FoundationModelsGateView(gate: foundationModelsGate)
            }
        }
        .frame(minWidth: 800, minHeight: 540)
        .onAppear {
            foundationModelsGate.refresh()
        }
    }

    private var mainTabs: some View {
        TabView {
            PlaybooksView()
                .tabItem {
                    Label("Playbooks", systemImage: "list.bullet.clipboard")
                }
                .accessibilityIdentifier("tab-playbooks")

            ManualToolboxView()
                .tabItem {
                    Label("Toolbox", systemImage: "wrench.and.screwdriver")
                }
                .accessibilityIdentifier("tab-toolbox")

            NavigationStack {
                ChatView()
            }
            .tabItem {
                Label("Chat", systemImage: "bubble.left.and.bubble.right")
            }
            .accessibilityIdentifier("tab-chat")
        }
    }
}

#Preview {
    ContentView()
        .environmentObject(FoundationModelsGateModel())
}
