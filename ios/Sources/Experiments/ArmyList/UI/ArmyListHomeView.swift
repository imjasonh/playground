import SwiftUI

/// Library of saved army lists.
struct ArmyListHomeView: View {
    @State private var store = ArmyListStore()
    @State private var lists: [ArmyListDocument] = []
    @State private var catalog: ArmyCatalog?
    @State private var loadError: String?
    /// False until `bootstrap` finishes. First paint must not look like an
    /// empty library with Create enabled while `catalog` is still nil.
    @State private var didBootstrap = false
    @State private var saveError: String?
    /// Sheet payload carries the catalog itself. Two `@State` vars
    /// (`sheetCatalog` + `.create`) raced on device: the sheet opened on
    /// `.create` before the snapshot landed → "without a catalog snapshot."
    @State private var newListSheet: NewListPresentation?
    /// Editor opened after Create. Catalog rides on the item (same race class
    /// as the New List sheet).
    @State private var editorPresentation: EditorPresentation?
    @State private var pendingEditorAfterSheet: EditorPresentation?
    /// `nil` means every faction.
    @State private var factionFilter: String?
    /// `nil` means every battle size / points level.
    @State private var battleSizeFilter: String?

    /// Identifiable New List sheet. The catalog (or error) travels with the
    /// item so `sheet(item:)` never renders against a second `@State`.
    struct NewListPresentation: Identifiable {
        let id = UUID()
        let catalog: ArmyCatalog?
        let errorMessage: String?

        static func create(_ catalog: ArmyCatalog) -> NewListPresentation {
            NewListPresentation(catalog: catalog, errorMessage: nil)
        }

        static func unavailable(_ message: String) -> NewListPresentation {
            NewListPresentation(catalog: nil, errorMessage: message)
        }
    }

    struct EditorPresentation: Identifiable {
        var id: UUID { list.id }
        let list: ArmyListDocument
        let catalog: ArmyCatalog
    }

    private var filteredLists: [ArmyListDocument] {
        // `loadAll` already sorts by most recently updated.
        lists.filter { list in
            if let factionFilter, list.factionID != factionFilter {
                return false
            }
            if let battleSizeFilter, list.battleSizeID != battleSizeFilter {
                return false
            }
            return true
        }
    }

    private var filtersActive: Bool {
        factionFilter != nil || battleSizeFilter != nil
    }

    private var canCreateList: Bool {
        didBootstrap && catalog != nil && loadError == nil
    }

    var body: some View {
        Group {
            if !didBootstrap {
                ProgressView("Loading catalog…")
                    .accessibilityIdentifier("armyListCatalogLoading")
                    .frame(maxWidth: .infinity, maxHeight: .infinity)
            } else if let loadError {
                unavailablePane(
                    systemImage: "exclamationmark.triangle",
                    title: "Catalog unavailable",
                    message: loadError
                )
                .accessibilityIdentifier("armyListCatalogUnavailable")
            } else if lists.isEmpty {
                unavailablePane(
                    systemImage: "shield.lefthalf.filled",
                    title: "No army lists",
                    message: "Create a list to get started."
                ) {
                    Button("New list") { presentNewList() }
                        .buttonStyle(.borderedProminent)
                        .disabled(!canCreateList)
                        .accessibilityIdentifier("armyListNewButton")
                }
                .accessibilityIdentifier("armyListEmptyState")
            } else {
                listContent
            }
        }
        .navigationTitle("Army List")
        .toolbar {
            ToolbarItem(placement: .primaryAction) {
                Button {
                    presentNewList()
                } label: {
                    Image(systemName: "plus")
                }
                .accessibilityLabel("New list")
                .accessibilityIdentifier("armyListNewButton")
                .disabled(!canCreateList)
            }
        }
        .sheet(item: $newListSheet, onDismiss: handleNewListSheetDismissed) { presentation in
            NavigationStack {
                if let catalog = presentation.catalog {
                    ArmyListNewSheet(catalog: catalog) { created in
                        createList(created)
                    }
                } else {
                    newListUnavailablePane(
                        message: presentation.errorMessage
                            ?? "The construction catalog is not loaded. Install a build that includes catalog.json in the app bundle."
                    )
                }
            }
            .accessibilityIdentifier("armyListNewSheet")
        }
        .fullScreenCover(item: $editorPresentation) { presentation in
            NavigationStack {
                ArmyListEditorView(
                    list: presentation.list,
                    catalog: presentation.catalog,
                    store: store
                ) {
                    reload()
                }
                .toolbar {
                    ToolbarItem(placement: .cancellationAction) {
                        Button("Done") {
                            editorPresentation = nil
                            reload()
                        }
                        .accessibilityIdentifier("armyListEditorDone")
                    }
                }
            }
            .accessibilityIdentifier("armyListEditorCover")
        }
        .alert("Could not save list", isPresented: Binding(
            get: { saveError != nil },
            set: { if !$0 { saveError = nil } }
        )) {
            Button("OK", role: .cancel) { saveError = nil }
        } message: {
            Text(saveError ?? "Unknown error.")
        }
        .onAppear(perform: bootstrap)
    }

    private func newListUnavailablePane(message: String) -> some View {
        unavailablePane(
            systemImage: "exclamationmark.triangle",
            title: "Cannot create a list",
            message: message
        )
        .accessibilityIdentifier("armyListNewSheetUnavailable")
        .navigationTitle("New list")
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .cancellationAction) {
                Button("Cancel") { newListSheet = nil }
                    .accessibilityIdentifier("armyListNewSheetCancel")
            }
        }
    }

    @ViewBuilder
    private var listContent: some View {
        List {
            if let catalog {
                Section {
                    Picker("Faction", selection: $factionFilter) {
                        Text("All factions").tag(String?.none)
                        ForEach(catalog.factions) { faction in
                            Text(faction.name).tag(Optional(faction.id))
                        }
                    }
                    .accessibilityIdentifier("armyListFactionFilter")

                    Picker("Points", selection: $battleSizeFilter) {
                        Text("All points levels").tag(String?.none)
                        ForEach(catalog.battleSizes) { size in
                            Text("\(size.name) (\(size.pointsLimit) pts)").tag(Optional(size.id))
                        }
                    }
                    .accessibilityIdentifier("armyListBattleSizeFilter")
                } header: {
                    Text("Filter")
                }
            }

            if filteredLists.isEmpty {
                Section {
                    VStack(alignment: .leading, spacing: 8) {
                        Text("No lists match these filters")
                            .font(.headline)
                        Text("Clear a filter or create a new list for this faction and points level.")
                            .font(.subheadline)
                            .foregroundStyle(.secondary)
                        if filtersActive {
                            Button("Clear filters") {
                                factionFilter = nil
                                battleSizeFilter = nil
                            }
                            .accessibilityIdentifier("armyListClearFiltersButton")
                        }
                    }
                    .padding(.vertical, 4)
                }
            } else {
                Section {
                    ForEach(filteredLists) { list in
                        NavigationLink {
                            if let catalog {
                                ArmyListEditorView(list: list, catalog: catalog, store: store) {
                                    reload()
                                }
                            } else {
                                unavailablePane(
                                    systemImage: "exclamationmark.triangle",
                                    title: "Could not open list",
                                    message: loadError
                                        ?? "The construction catalog is not loaded."
                                )
                                .accessibilityIdentifier("armyListEditorUnavailable")
                            }
                        } label: {
                            ArmyListRowView(list: list, catalog: catalog)
                        }
                        .accessibilityIdentifier("armyListRow-\(list.id.uuidString)")
                    }
                    .onDelete(perform: deleteFiltered)
                }
            }
        }
        .accessibilityIdentifier("armyListLibrary")
    }

    private func unavailablePane(
        systemImage: String,
        title: String,
        message: String,
        @ViewBuilder actions: () -> some View = { EmptyView() }
    ) -> some View {
        VStack(spacing: 12) {
            Image(systemName: systemImage)
                .font(.largeTitle)
                .foregroundStyle(.secondary)
                .accessibilityHidden(true)
            Text(title)
                .font(.headline)
            Text(message)
                .font(.subheadline)
                .foregroundStyle(.secondary)
                .multilineTextAlignment(.center)
            actions()
        }
        .padding()
        .frame(maxWidth: .infinity, maxHeight: .infinity)
    }

    private func bootstrap() {
        defer { didBootstrap = true }
        do {
            catalog = try CatalogLoader.load()
            loadError = nil
            reload()
        } catch {
            catalog = nil
            loadError = error.localizedDescription
        }
    }

    private func presentNewList() {
        guard didBootstrap else { return }
        if let catalog {
            newListSheet = .create(catalog)
        } else {
            newListSheet = .unavailable(
                loadError
                    ?? "The construction catalog is not loaded. Install a build that includes catalog.json in the app bundle."
            )
        }
    }

    private func createList(_ created: ArmyListDocument) {
        guard let catalog else {
            saveError = loadError
                ?? "The construction catalog is not loaded, so the list cannot be opened in the editor."
            return
        }
        do {
            try store.save(created)
            reload()
            // Hold the editor payload until the create sheet's onDismiss; the
            // catalog is already on the payload so the cover cannot open empty.
            pendingEditorAfterSheet = EditorPresentation(list: created, catalog: catalog)
            newListSheet = nil
        } catch {
            saveError = error.localizedDescription
        }
    }

    private func handleNewListSheetDismissed() {
        guard let pending = pendingEditorAfterSheet else { return }
        pendingEditorAfterSheet = nil
        editorPresentation = pending
    }

    private func reload() {
        let loaded = store.loadAll()
        guard let catalog else {
            lists = loaded
            return
        }
        lists = loaded.map { document in
            var upgraded = document
            if upgraded.applyCatalogUpgrade(using: catalog) {
                try? store.save(upgraded)
            }
            return upgraded
        }
    }

    private func deleteFiltered(at offsets: IndexSet) {
        let snapshot = filteredLists
        for index in offsets {
            try? store.delete(snapshot[index])
        }
        reload()
    }
}

private struct ArmyListRowView: View {
    let list: ArmyListDocument
    let catalog: ArmyCatalog?

    var body: some View {
        let validation = catalog.map { ArmyListValidator.validate(list: list, catalog: $0) }
        return VStack(alignment: .leading, spacing: 4) {
            HStack(alignment: .firstTextBaseline) {
                Text(list.name)
                    .font(.headline)
                Spacer(minLength: 8)
                if let validation {
                    Text(validation.isLegal ? "Legal" : "Illegal")
                        .font(.caption.weight(.semibold))
                        .foregroundStyle(validation.isLegal ? Color.green : Color.red)
                        .accessibilityLabel(validation.isLegal ? "Legal list" : "Illegal list")
                }
            }
            HStack(spacing: 8) {
                Text(factionName)
                    .font(.subheadline)
                    .foregroundStyle(.secondary)
                Text(battleSizeLabel)
                    .font(.caption)
                    .foregroundStyle(.secondary)
                if let validation {
                    Text("\(validation.totalPoints) pts")
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

    private var battleSizeLabel: String {
        guard let size = catalog?.battleSize(id: list.battleSizeID) else {
            return list.battleSizeID
        }
        return "\(size.name) · \(size.pointsLimit)"
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

    private var factionsSorted: [FactionDefinition] {
        catalog.factions.sorted {
            $0.name.localizedCaseInsensitiveCompare($1.name) == .orderedAscending
        }
    }

    private var canSubmit: Bool {
        !factionID.isEmpty && catalog.battleSize(id: battleSizeID) != nil
    }

    init(catalog: ArmyCatalog, onCreate: @escaping (ArmyListDocument) -> Void) {
        self.catalog = catalog
        self.onCreate = onCreate
        let defaultFaction = catalog.factions
            .sorted { $0.name.localizedCaseInsensitiveCompare($1.name) == .orderedAscending }
            .first?.id
            ?? ""
        _factionID = State(initialValue: defaultFaction)
    }

    var body: some View {
        Form {
            if factionsSorted.isEmpty {
                Section {
                    Text("This catalog has no factions, so a list cannot be created.")
                        .foregroundStyle(.secondary)
                        .accessibilityIdentifier("armyListNewSheetEmptyCatalog")
                }
            }

            Section("Name") {
                TextField("List name", text: $name)
                    .accessibilityIdentifier("armyListNameField")
            }
            Section("Faction") {
                Picker("Faction", selection: $factionID) {
                    ForEach(factionsSorted) { faction in
                        Text(faction.name).tag(faction.id)
                    }
                }
                .disabled(factionsSorted.isEmpty)
                .accessibilityIdentifier("armyListFactionPicker")
            }
            Section("Battle size") {
                Picker("Battle size", selection: $battleSizeID) {
                    ForEach(catalog.battleSizes) { size in
                        Text("\(size.name) (\(size.pointsLimit))").tag(size.id)
                    }
                }
                .disabled(catalog.battleSizes.isEmpty)
                .accessibilityIdentifier("armyListBattleSizePicker")
            }
        }
        .navigationTitle("New list")
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .cancellationAction) {
                Button("Cancel") { dismiss() }
                    .accessibilityIdentifier("armyListNewSheetCancel")
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
                .disabled(!canSubmit)
                .accessibilityIdentifier("armyListCreateButton")
            }
        }
    }
}
