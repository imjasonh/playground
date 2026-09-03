import SwiftUI

/// Library of saved army lists.
struct ArmyListHomeView: View {
    @State private var store = ArmyListStore()
    @State private var lists: [ArmyListDocument] = []
    @State private var catalog: ArmyCatalog?
    @State private var loadError: String?
    @State private var showNewList = false

    var body: some View {
        Group {
            if let loadError {
                VStack(spacing: 12) {
                    Image(systemName: "exclamationmark.triangle")
                        .font(.largeTitle)
                        .foregroundStyle(.secondary)
                        .accessibilityHidden(true)
                    Text("Catalog unavailable")
                        .font(.headline)
                    Text(loadError)
                        .font(.subheadline)
                        .foregroundStyle(.secondary)
                        .multilineTextAlignment(.center)
                }
                .padding()
                .frame(maxWidth: .infinity, maxHeight: .infinity)
            } else if lists.isEmpty {
                VStack(spacing: 12) {
                    Image(systemName: "shield.lefthalf.filled")
                        .font(.largeTitle)
                        .foregroundStyle(.secondary)
                        .accessibilityHidden(true)
                    Text("No army lists")
                        .font(.headline)
                    Text("Build an 11th Edition list for any faction and validate it against construction rules from the Munitorum Field Manual.")
                        .font(.subheadline)
                        .foregroundStyle(.secondary)
                        .multilineTextAlignment(.center)
                    Button("New list") { showNewList = true }
                        .buttonStyle(.borderedProminent)
                        .accessibilityIdentifier("armyListNewButton")
                }
                .padding()
                .frame(maxWidth: .infinity, maxHeight: .infinity)
            } else {
                List {
                    Section {
                        ForEach(lists) { list in
                            NavigationLink {
                                if let catalog {
                                    ArmyListEditorView(list: list, catalog: catalog, store: store) {
                                        reload()
                                    }
                                }
                            } label: {
                                ArmyListRowView(list: list, catalog: catalog)
                            }
                            .accessibilityIdentifier("armyListRow-\(list.id.uuidString)")
                        }
                        .onDelete(perform: delete)
                    } footer: {
                        catalogFooter
                    }
                }
            }
        }
        .navigationTitle("Army List")
        .toolbar {
            ToolbarItem(placement: .primaryAction) {
                Button {
                    showNewList = true
                } label: {
                    Image(systemName: "plus")
                }
                .accessibilityLabel("New list")
                .accessibilityIdentifier("armyListNewButton")
            }
        }
        .sheet(isPresented: $showNewList) {
            if let catalog {
                NavigationStack {
                    ArmyListNewSheet(catalog: catalog) { created in
                        try? store.save(created)
                        showNewList = false
                        reload()
                    }
                }
            }
        }
        .onAppear(perform: bootstrap)
    }

    @ViewBuilder
    private var catalogFooter: some View {
        if let catalog {
            Text("Catalog \(catalog.version). Unofficial fan experiment — confirm with the Munitorum Field Manual for events.")
                .font(.footnote)
        }
    }

    private func bootstrap() {
        do {
            catalog = try CatalogLoader.load()
            reload()
        } catch {
            loadError = error.localizedDescription
        }
    }

    private func reload() {
        lists = store.loadAll()
    }

    private func delete(at offsets: IndexSet) {
        for index in offsets {
            try? store.delete(lists[index])
        }
        reload()
    }
}

private struct ArmyListRowView: View {
    let list: ArmyListDocument
    let catalog: ArmyCatalog?

    var body: some View {
        VStack(alignment: .leading, spacing: 4) {
            Text(list.name)
                .font(.headline)
            HStack(spacing: 8) {
                Text(factionName)
                    .font(.subheadline)
                    .foregroundStyle(.secondary)
                if let catalog {
                    let result = ArmyListValidator.validate(list: list, catalog: catalog)
                    Text(result.isLegal ? "Legal" : "Illegal")
                        .font(.caption.weight(.semibold))
                        .foregroundStyle(result.isLegal ? Color.green : Color.red)
                    Text("\(result.totalPoints) pts")
                        .font(.caption)
                        .foregroundStyle(.secondary)
                }
            }
        }
        .padding(.vertical, 2)
    }

    private var factionName: String {
        catalog?.faction(id: list.factionID)?.name ?? list.factionID
    }
}

/// Create a blank list: faction, battle size, name.
struct ArmyListNewSheet: View {
    let catalog: ArmyCatalog
    var onCreate: (ArmyListDocument) -> Void

    @Environment(\.dismiss) private var dismiss
    @State private var name = "New list"
    @State private var factionID: String
    @State private var battleSizeID = "incursion"

    init(catalog: ArmyCatalog, onCreate: @escaping (ArmyListDocument) -> Void) {
        self.catalog = catalog
        self.onCreate = onCreate
        let defaultFaction = catalog.faction(id: "leagues-of-votann")?.id
            ?? catalog.factions.first?.id
            ?? "leagues-of-votann"
        _factionID = State(initialValue: defaultFaction)
    }

    var body: some View {
        Form {
            Section("Name") {
                TextField("List name", text: $name)
                    .accessibilityIdentifier("armyListNameField")
            }
            Section("Faction") {
                Picker("Faction", selection: $factionID) {
                    ForEach(catalog.factions) { faction in
                        Text(faction.name).tag(faction.id)
                    }
                }
                .accessibilityIdentifier("armyListFactionPicker")
            }
            Section("Battle size") {
                Picker("Battle size", selection: $battleSizeID) {
                    ForEach(catalog.battleSizes) { size in
                        Text("\(size.name) (\(size.pointsLimit))").tag(size.id)
                    }
                }
                .accessibilityIdentifier("armyListBattleSizePicker")
            }
            Section {
                Text("Points, Detachment Points, enhancements, and duplicates come from the Munitorum Field Manual snapshot bundled with this build.")
                    .font(.footnote)
                    .foregroundStyle(.secondary)
            }
        }
        .navigationTitle("New list")
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .cancellationAction) {
                Button("Cancel") { dismiss() }
            }
            ToolbarItem(placement: .confirmationAction) {
                Button("Create") {
                    let trimmed = name.trimmingCharacters(in: .whitespacesAndNewlines)
                    let list = ArmyListDocument(
                        name: trimmed.isEmpty ? "New list" : trimmed,
                        catalogVersion: catalog.version,
                        factionID: factionID,
                        battleSizeID: battleSizeID
                    )
                    onCreate(list)
                }
                .accessibilityIdentifier("armyListCreateButton")
            }
        }
    }
}
