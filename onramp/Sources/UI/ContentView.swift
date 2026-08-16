import SwiftUI

struct ContentView: View {
    var body: some View {
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
        .frame(minWidth: 800, minHeight: 540)
    }
}

#Preview {
    ContentView()
}
