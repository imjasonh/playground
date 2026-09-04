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
    /// One presentation item for Create and the post-create editor. Catalog
    /// (or error text) lives on the case — never a second `@State` the cover
    /// body has to read. Create → editor is just replacing this value.
    @State private var presentation: Presentation?
    /// `nil` means every faction.
    @State private var factionFilter: String?
    /// `nil` means every battle size / points level.
    @State private var battleSizeFilter: String?

    /// Full-screen flows owned by the home screen. Every case carries what
    /// the UI needs so `fullScreenCover(item:)` cannot open empty.
    enum Presentation: Identifiable {
        case create(ArmyCatalog)
        case unavailable(String)
        case editor(list: ArmyListDocument, catalog: ArmyCatalog)

        var id: String {
            switch self {
            case .create:
                return "create"
            case .unavailable:
                return "unavailable"
            case .editor(let list, _):
                return "editor-\(list.id.uuidString)"
            }
        }
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
        .fullScreenCover(item: $presentation) { item in
            presentationCover(item)
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

    @ViewBuilder
    private func presentationCover(_ item: Presentation) -> some View {
        switch item {
        case .create(let catalog):
            NavigationStack {
                ArmyListNewSheet(catalog: catalog) { created in
                    createList(created, catalog: catalog)
                }
            }
            .accessibilityIdentifier("armyListNewSheet")

        case .unavailable(let message):
            NavigationStack {
                newListUnavailablePane(message: message)
            }
            .accessibilityIdentifier("armyListNewSheet")

        case .editor(let list, let catalog):
            NavigationStack {
                ArmyListEditorView(
                    list: list,
                    catalog: catalog,
                    store: store
                ) {
                    reload()
                }
                .toolbar {
                    ToolbarItem(placement: .cancellationAction) {
                        Button("Done") {
                            presentation = nil
                            reload()
                        }
                        .accessibilityIdentifier("armyListEditorDone")
                    }
                }
            }
            .accessibilityIdentifier("armyListEditorCover")
        }
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
                Button("Cancel") { presentation = nil }
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
                        if let catalog {
                            NavigationLink {
                                ArmyListEditorView(list: list, catalog: catalog, store: store) {
                                    reload()
                                }
                            } label: {
                                ArmyListRowView(list: list, catalog: catalog)
                            }
                            .accessibilityIdentifier("armyListRow-\(list.id.uuidString)")
                        }
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
            presentation = .create(catalog)
        } else {
            presentation = .unavailable(
                loadError
                    ?? "The construction catalog is not loaded. Install a build that includes catalog.json in the app bundle."
            )
        }
    }

    private func createList(_ created: ArmyListDocument, catalog: ArmyCatalog) {
        do {
            try store.save(created)
            reload()
            // Same `presentation` value → editor. No pending handoff, no second
            // cover, no catalog looked up from another `@State`.
            presentation = .editor(list: created, catalog: catalog)
        } catch {
            saveError = error.localizedDescription
        }
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
                    ArmyListIssueCountsLabel(
                        errors: validation.errors.count,
                        warnings: validation.warnings.count,
                        style: .caption2
                    )
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

/// Create a blank list or a seeded starter: faction, battle size, detachments, name.
struct ArmyListNewSheet: View {
    let catalog: ArmyCatalog
    var onCreate: (ArmyListDocument) -> Void

    @Environment(\.dismiss) private var dismiss
    @State private var name = "New list"
    @State private var factionID: String
    @State private var battleSizeID = "incursion"
    @State private var selectedDetachmentIDs: Set<String> = []
    @State private var seedError: String?

    private var factionsSorted: [FactionDefinition] {
        catalog.factions.sorted {
            $0.name.localizedCaseInsensitiveCompare($1.name) == .orderedAscending
        }
    }

    private var factionDetachments: [DetachmentDefinition] {
        catalog.detachments
            .filter { $0.factionID == factionID }
            .sorted {
                $0.name.localizedCaseInsensitiveCompare($1.name) == .orderedAscending
            }
    }

    private var detachmentPointsBudget: Int {
        catalog.battleSize(id: battleSizeID)?.detachmentPointsBudget ?? 0
    }

    private var detachmentPointsSpent: Int {
        factionDetachments
            .filter { selectedDetachmentIDs.contains($0.id) }
            .reduce(0) { $0 + $1.detachmentPoints }
    }

    private var canSubmit: Bool {
        !factionID.isEmpty
            && catalog.battleSize(id: battleSizeID) != nil
            && !selectedDetachmentIDs.isEmpty
            && detachmentPointsSpent <= detachmentPointsBudget
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
                .onChange(of: factionID) { _ in
                    selectedDetachmentIDs.removeAll()
                }
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

            Section {
                if factionDetachments.isEmpty {
                    Text("No detachments for this faction.")
                        .foregroundStyle(.secondary)
                } else {
                    ForEach(factionDetachments) { detachment in
                        Toggle(isOn: bindingForDetachment(detachment.id)) {
                            VStack(alignment: .leading, spacing: 2) {
                                Text(detachment.name)
                                Text("\(detachment.detachmentPoints) DP · \(detachment.forceDisposition)")
                                    .font(.caption)
                                    .foregroundStyle(.secondary)
                                if let tag = detachment.uniqueTag {
                                    Text("Unique: \(tag)")
                                        .font(.caption2)
                                        .foregroundStyle(.orange)
                                }
                            }
                        }
                        .accessibilityIdentifier("armyListNewDetachment-\(detachment.id)")
                    }
                }
            } header: {
                Text("Detachments")
            } footer: {
                Text("\(detachmentPointsSpent) / \(detachmentPointsBudget) DP. Build starter list fills units for these picks.")
                    .accessibilityIdentifier("armyListNewDetachmentPoints")
            }

            if let seedError {
                Section {
                    Text(seedError)
                        .foregroundStyle(.red)
                        .accessibilityIdentifier("armyListBuildStarterError")
                }
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
                    createBlankList()
                }
                .disabled(!canSubmit)
                .accessibilityIdentifier("armyListCreateButton")
            }
            ToolbarItem(placement: .bottomBar) {
                Button("Build starter list") {
                    createStarterList()
                }
                .disabled(!canSubmit)
                .accessibilityIdentifier("armyListBuildStarterButton")
            }
        }
    }

    private func bindingForDetachment(_ id: String) -> Binding<Bool> {
        Binding(
            get: { selectedDetachmentIDs.contains(id) },
            set: { isOn in
                if isOn {
                    selectedDetachmentIDs.insert(id)
                } else {
                    selectedDetachmentIDs.remove(id)
                }
            }
        )
    }

    private func trimmedName() -> String? {
        let trimmed = name.trimmingCharacters(in: .whitespacesAndNewlines)
        if trimmed.isEmpty || trimmed == "New list" {
            return nil
        }
        return trimmed
    }

    private func orderedDetachmentIDs() -> [String] {
        factionDetachments
            .map(\.id)
            .filter { selectedDetachmentIDs.contains($0) }
    }

    private func createBlankList() {
        seedError = nil
        let list = ArmyListDocument(
            name: trimmedName() ?? "New list",
            catalogVersion: catalog.version,
            factionID: factionID,
            battleSizeID: battleSizeID,
            detachmentIDs: orderedDetachmentIDs()
        )
        onCreate(list)
    }

    private func createStarterList() {
        seedError = nil
        guard let seeded = ArmyListLegalSeeder.seed(
            catalog: catalog,
            factionID: factionID,
            battleSizeID: battleSizeID,
            name: trimmedName(),
            detachmentIDs: orderedDetachmentIDs()
        ) else {
            seedError = "Couldn’t build a starter list for this faction, battle size, and detachments."
            return
        }
        onCreate(seeded.list)
    }
}

