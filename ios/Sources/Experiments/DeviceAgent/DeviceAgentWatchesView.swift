import AppIntents
import SwiftUI

/// Long-running watches, Shortcuts Automation setup, and Siri tips.
struct DeviceAgentWatchesView: View {
    @ObservedObject var store: AgentWatchStore
    @Environment(\.dismiss) private var dismiss

    @State private var title = ""
    @State private var prompt = ""
    @State private var intervalHours: Double = 24

    var body: some View {
        List {
            automationSection
            siriSection
            watchesSection
            addSection
        }
        .navigationTitle("Watches")
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .cancellationAction) {
                Button("Done") { dismiss() }
                    .accessibilityIdentifier("deviceAgentWatchesDone")
            }
        }
        .accessibilityIdentifier("deviceAgentWatchesSheet")
    }

    private var automationSection: some View {
        Section {
            Text(store.lastAutomaticCheckSummary)
                .font(.subheadline)
                .foregroundStyle(.secondary)
                .accessibilityIdentifier("deviceAgentWatchLastCheck")

            if store.needsAutomationNudge {
                Text(store.isAutomaticCheckStale
                    ? "No automatic check arrived in time. The Automation may be off, needing confirmation, or deleted."
                    : "Add one repeating Automation that runs “Check Device Agent watches”. Device Agent keeps the watch list; you only set the schedule once.")
                    .font(.footnote)
            }

            Button("Open Shortcuts") {
                store.openShortcutsApp()
            }
            .accessibilityIdentifier("deviceAgentOpenShortcuts")

            Toggle(
                "I’ve set up a repeating Automation",
                isOn: $store.userMarkedAutomationConfigured
            )
            .accessibilityIdentifier("deviceAgentAutomationConfiguredToggle")

            Text("""
            In Shortcuts: Automation → New → Time of Day (or another trigger) → \
            Add Action → Check Device Agent watches → turn on Run Immediately if offered.
            """)
            .font(.caption)
            .foregroundStyle(.secondary)
        } header: {
            Text("Automation wake")
        }
    }

    private var siriSection: some View {
        Section {
            SiriTipView(intent: CheckDeviceAgentWatchesIntent())
                .siriTipViewStyle(.automatic)
            ShortcutsLink()
                .shortcutsLinkStyle(.automatic)
        } header: {
            Text("Siri")
        } footer: {
            Text("Say “Check Device Agent watches in Playground” or “Ask Device Agent in Playground …”. App Shortcuts appear after install; no Shortcuts authoring required for those phrases.")
        }
    }

    private var watchesSection: some View {
        Section {
            if store.watches.isEmpty {
                Text("No watches yet. Add one below — then set up the Automation so it can wake on a schedule.")
                    .font(.footnote)
                    .foregroundStyle(.secondary)
            } else {
                ForEach(store.watches) { watch in
                    VStack(alignment: .leading, spacing: 4) {
                        HStack {
                            Text(watch.title)
                                .font(.headline)
                            Spacer()
                            if watch.isPaused {
                                Text("Paused")
                                    .font(.caption)
                                    .foregroundStyle(.secondary)
                            } else if watch.isDue() {
                                Text("Due")
                                    .font(.caption.weight(.semibold))
                                    .foregroundStyle(.orange)
                            }
                        }
                        Text(watch.prompt)
                            .font(.footnote)
                            .foregroundStyle(.secondary)
                        Text("Every \(Int(watch.intervalHours))h")
                            .font(.caption2)
                            .foregroundStyle(.secondary)
                        HStack {
                            Button(watch.isPaused ? "Resume" : "Pause") {
                                store.setPaused(id: watch.id, paused: !watch.isPaused)
                            }
                            .buttonStyle(.bordered)
                            Button("Remove", role: .destructive) {
                                store.removeWatch(id: watch.id)
                            }
                            .buttonStyle(.bordered)
                        }
                        .padding(.top, 2)
                    }
                    .accessibilityIdentifier("deviceAgentWatchRow-\(watch.id.uuidString)")
                }
            }
        } header: {
            Text("Watch list")
        }
    }

    private var addSection: some View {
        Section {
            TextField("Title", text: $title)
                .accessibilityIdentifier("deviceAgentWatchTitleField")
            TextField("What should Device Agent check?", text: $prompt, axis: .vertical)
                .lineLimit(2...5)
                .accessibilityIdentifier("deviceAgentWatchPromptField")
            Stepper(value: $intervalHours, in: 1...168, step: 1) {
                Text("Every \(Int(intervalHours)) hours")
            }
            .accessibilityIdentifier("deviceAgentWatchIntervalStepper")
            Button("Add watch") {
                store.addWatch(title: title, prompt: prompt, intervalHours: intervalHours)
                title = ""
                prompt = ""
            }
            .disabled(
                title.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty
                    || prompt.trimmingCharacters(in: .whitespacesAndNewlines).isEmpty
            )
            .accessibilityIdentifier("deviceAgentAddWatchButton")
        } header: {
            Text("Add watch")
        }
    }
}
