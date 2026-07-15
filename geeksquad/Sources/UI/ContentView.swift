import SwiftUI

struct ContentView: View {
    var body: some View {
        TabView {
            NavigationStack {
                ChatView()
            }
            .tabItem {
                Label("Chat", systemImage: "bubble.left.and.bubble.right")
            }
            .accessibilityIdentifier("tab-chat")

            ManualToolboxView()
                .tabItem {
                    Label("Toolbox", systemImage: "wrench.and.screwdriver")
                }
                .accessibilityIdentifier("tab-toolbox")
        }
        .frame(minWidth: 760, minHeight: 520)
    }
}

#Preview {
    ContentView()
}
