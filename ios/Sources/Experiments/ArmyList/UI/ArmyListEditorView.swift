import SwiftUI

/// Authoring surface: detachments, units, live validation, share.
struct ArmyListEditorView: View {
    @State private var list: ArmyListDocument
    let catalog: ArmyCatalog
    let store: ArmyListStore
    var onChange: () -> Void

    @State private var showAddUnit = false
    /// Item-based share sheet so we never present an empty modal while text/URL
    /// state is still being filled in.
    @State private var sharePayload: SharePayload?

    private struct SharePayload: Identifiable {
        let id = UUID()
        let text: String
        let fileURL: URL?
    }

    init(
        list: ArmyListDocument,
        catalog: ArmyCatalog,
        store: ArmyListStore,
        onChange: @escaping () -> Void
    ) {
        _list = State(initialValue: list)
        self.catalog = catalog
        self.store = store
        self.onChange = onChange
    }

    private var validation: ValidationResult {
        ArmyListValidator.validate(list: list, catalog: catalog)
    }

    var body: some View {
        List {
            Section {
                validationBanner
                pointsRow
            }

            Section("Name") {
                TextField("List name", text: $list.name)
                    .textInputAutocapitalization(.words)
                    .accessibilityIdentifier("armyListEditorNameField")
            }

            Section("Battle size") {
                Picker("Battle size", selection: $list.battleSizeID) {
                    ForEach(catalog.battleSizes) { size in
                        Text("\(size.name) (\(size.pointsLimit))").tag(size.id)
                    }
                }
                .accessibilityIdentifier("armyListEditorBattleSizePicker")
            }

            Section("Detachments") {
                ForEach(catalog.detachments.filter { $0.factionID == list.factionID }) { detachment in
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
                    .accessibilityIdentifier("armyListDetachment-\(detachment.id)")
                }
            }

            Section("Units") {
                ForEach(list.units) { unit in
                    NavigationLink {
                        ArmyListUnitDetailView(
                            list: $list,
                            unitID: unit.id,
                            catalog: catalog
                        )
                        .onDisappear(perform: persist)
                    } label: {
                        unitRow(unit)
                    }
                    .swipeActions(edge: .trailing, allowsFullSwipe: true) {
                        Button(role: .destructive) {
                            deleteUnit(id: unit.id)
                        } label: {
                            Label("Delete", systemImage: "trash")
                        }
                        .accessibilityIdentifier("armyListDeleteUnit-\(unit.id.uuidString)")

                        Button {
                            duplicateUnit(id: unit.id)
                        } label: {
                            Label("Duplicate", systemImage: "plus.square.on.square")
                        }
                        .tint(.indigo)
                        .accessibilityIdentifier("armyListDuplicateUnit-\(unit.id.uuidString)")
                    }
                }

                Button {
                    showAddUnit = true
                } label: {
                    Label("Add unit", systemImage: "plus.circle")
                }
                .accessibilityIdentifier("armyListAddUnitButton")
            }

            Section("Warlord") {
                Picker("Warlord", selection: warlordBinding) {
                    Text("None").tag(UUID?.none)
                    ForEach(characterUnits) { unit in
                        Text(catalog.datasheet(id: unit.datasheetID)?.name ?? unit.datasheetID)
                            .tag(Optional(unit.id))
                    }
                }
                .accessibilityIdentifier("armyListWarlordPicker")
            }

            Section("Notes") {
                TextField("Notes", text: $list.notes, axis: .vertical)
                    .lineLimit(3...6)
            }
        }
        .navigationTitle(list.name)
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .primaryAction) {
                NavigationLink {
                    ArmyListChatView(list: $list, catalog: catalog, store: store)
                } label: {
                    Image(systemName: "bubble.left.and.bubble.right")
                }
                .accessibilityLabel("List chat")
                .accessibilityIdentifier("armyListChatButton")
            }
            ToolbarItem(placement: .primaryAction) {
                Button {
                    sharePayload = makeSharePayload()
                } label: {
                    Image(systemName: "square.and.arrow.up")
                }
                .accessibilityLabel("Share list")
                .accessibilityIdentifier("armyListShareButton")
            }
        }
        .sheet(isPresented: $showAddUnit) {
            NavigationStack {
                ArmyListUnitPickerView(catalog: catalog, factionID: list.factionID) { sheet in
                    let models = sheet.modelCounts.first ?? sheet.minModels
                    list.units.append(
                        ListUnitInstance(
                            datasheetID: sheet.id,
                            models: models,
                            optionIDs: sheet.defaultOptionIDs()
                        )
                    )
                    showAddUnit = false
                    persist()
                }
            }
            .accessibilityIdentifier("armyListAddUnitSheet")
        }
        .sheet(item: $sharePayload) { payload in
            ShareArmyListSheet(text: payload.text, fileURL: payload.fileURL)
                .accessibilityIdentifier("armyListShareSheet")
        }
        .onAppear {
            if list.applyCatalogUpgrade(using: catalog) {
                persist()
            }
        }
        .onChange(of: list) { _ in
            persist()
        }
    }

    private var characterUnits: [ListUnitInstance] {
        list.units.filter {
            catalog.datasheet(id: $0.datasheetID)?.characterRole != nil
        }
    }

    private var warlordBinding: Binding<UUID?> {
        Binding(
            get: { list.warlordUnitID },
            set: { list.warlordUnitID = $0 }
        )
    }

    private var validationBanner: some View {
        let result = validation
        return VStack(alignment: .leading, spacing: 6) {
            HStack {
                Text(result.isLegal ? "Legal" : "Illegal")
                    .font(.headline)
                    .foregroundStyle(result.isLegal ? Color.green : Color.red)
                    .accessibilityIdentifier("armyListLegalBadge")
                Spacer()
                ArmyListIssueCountsLabel(
                    errors: result.errors.count,
                    warnings: result.warnings.count
                )
            }
            ForEach(result.issues.prefix(8)) { issue in
                Text("\(issue.severity == .error ? "•" : "◦") \(issue.message)")
                    .font(.caption)
                    .foregroundStyle(issue.severity == .error ? Color.primary : Color.secondary)
            }
            if result.issues.count > 8 {
                Text("+\(result.issues.count - 8) more")
                    .font(.caption2)
                    .foregroundStyle(.secondary)
            }
        }
        .accessibilityIdentifier("armyListValidationBanner")
    }

    private var pointsRow: some View {
        let result = validation
        let battle = catalog.battleSize(id: list.battleSizeID)
        return HStack {
            Label("\(result.totalPoints) / \(battle?.pointsLimit ?? 0) pts", systemImage: "number")
            Spacer()
            Text("DP \(result.detachmentPointsSpent)/\(battle?.detachmentPointsBudget ?? 0)")
                .foregroundStyle(.secondary)
        }
        .font(.subheadline)
        .accessibilityIdentifier("armyListPointsRow")
    }

    private func unitRow(_ unit: ListUnitInstance) -> some View {
        let sheet = catalog.datasheet(id: unit.datasheetID)
        let copyIndex = list.units
            .prefix(while: { $0.id != unit.id })
            .filter { $0.datasheetID == unit.datasheetID }
            .count + 1
        let pts = sheet?.points(models: unit.models, copyIndex: copyIndex)
        return VStack(alignment: .leading, spacing: 2) {
            Text(sheet?.name ?? unit.datasheetID)
            HStack {
                Text("\(unit.models) models")
                if let pts {
                    Text("· \(pts) pts")
                }
                if unit.attachedToUnitID != nil {
                    Text("· attached")
                }
            }
            .font(.caption)
            .foregroundStyle(.secondary)
        }
    }

    private func bindingForDetachment(_ id: String) -> Binding<Bool> {
        Binding(
            get: { list.detachmentIDs.contains(id) },
            set: { enabled in
                if enabled {
                    if !list.detachmentIDs.contains(id) {
                        list.detachmentIDs.append(id)
                    }
                } else {
                    list.detachmentIDs.removeAll { $0 == id }
                    // Drop enhancements that required the removed detachment.
                    for index in list.units.indices {
                        list.units[index].enhancementIDs.removeAll { enhancementID in
                            guard let (detachment, _) = catalog.enhancement(id: enhancementID) else {
                                return false
                            }
                            return detachment.id == id
                        }
                    }
                }
            }
        )
    }

    private func deleteUnit(id: UUID) {
        let removedIDs: Set<UUID> = [id]
        list.units.removeAll { $0.id == id }
        list.units = list.units.map { unit in
            var copy = unit
            if let attached = copy.attachedToUnitID, removedIDs.contains(attached) {
                copy.attachedToUnitID = nil
            }
            return copy
        }
        if list.warlordUnitID == id {
            list.warlordUnitID = nil
        }
    }

    private func duplicateUnit(id: UUID) {
        _ = list.duplicateUnit(id: id)
    }

    private func persist() {
        try? store.save(list)
        onChange()
    }

    private func makeSharePayload() -> SharePayload {
        let result = validation
        let text = ArmyListTextExporter.text(for: list, catalog: catalog, validation: result)
        var fileURL: URL?
        if let data = try? ArmyListJSONExporter.data(for: list, validation: result) {
            let url = FileManager.default.temporaryDirectory
                .appendingPathComponent(ArmyListJSONExporter.filename(for: list))
            try? data.write(to: url, options: .atomic)
            fileURL = url
        }
        return SharePayload(text: text, fileURL: fileURL)
    }
}

struct ArmyListUnitPickerView: View {
    let catalog: ArmyCatalog
    let factionID: String
    var onPick: (DatasheetDefinition) -> Void

    @Environment(\.dismiss) private var dismiss
    @State private var query = ""
    /// Legends datasheets are hidden unless the player turns this on.
    @State private var includeLegends = false
    @State private var typeFilter: ArmyListUnitTypeFilter = .all

    private var sheets: [DatasheetDefinition] {
        ArmyListUnitPickerFiltering.sheets(
            from: catalog,
            factionID: factionID,
            query: query,
            includeLegends: includeLegends,
            typeFilter: typeFilter
        )
    }

    private var filtersActive: Bool {
        includeLegends || typeFilter != .all
    }

    var body: some View {
        List {
            Section {
                Toggle("Include Legends", isOn: $includeLegends)
                    .accessibilityIdentifier("armyListIncludeLegendsToggle")

                Picker("Type", selection: $typeFilter) {
                    ForEach(ArmyListUnitTypeFilter.allCases) { filter in
                        Text(filter.title).tag(filter)
                    }
                }
                .accessibilityIdentifier("armyListUnitTypeFilter")
            }

            Section {
                if sheets.isEmpty {
                    Text(emptyMessage)
                        .foregroundStyle(.secondary)
                        .accessibilityIdentifier("armyListUnitPickerEmpty")
                } else {
                    ForEach(sheets) { sheet in
                        Button {
                            onPick(sheet)
                        } label: {
                            VStack(alignment: .leading, spacing: 2) {
                                Text(sheet.name)
                                    .foregroundStyle(.primary)
                                HStack(spacing: 6) {
                                    if sheet.legends {
                                        Text("Legends")
                                    }
                                    if sheet.battleline {
                                        Text("Battleline")
                                    }
                                    if sheet.characterRole != nil {
                                        Text("Character")
                                    }
                                    if sheet.dedicatedTransport {
                                        Text("Transport")
                                    }
                                    if let pts = sheet.points(models: sheet.minModels, copyIndex: 1) {
                                        Text("\(pts)+ pts")
                                    }
                                }
                                .font(.caption)
                                .foregroundStyle(.secondary)
                            }
                        }
                        .accessibilityIdentifier("armyListPick-\(sheet.id)")
                    }
                }
            }
        }
        .searchable(text: $query, prompt: "Datasheets")
        .navigationTitle("Add unit")
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .cancellationAction) {
                Button("Cancel") { dismiss() }
            }
            ToolbarItem(placement: .primaryAction) {
                if filtersActive {
                    Button("Reset filters") {
                        includeLegends = false
                        typeFilter = .all
                    }
                    .accessibilityIdentifier("armyListUnitPickerResetFilters")
                }
            }
        }
    }

    private var emptyMessage: String {
        if !query.isEmpty || filtersActive {
            return "No datasheets match these filters."
        }
        return "No datasheets for this faction."
    }
}

enum ArmyListUnitTypeFilter: String, CaseIterable, Identifiable, Sendable {
    case all
    case battleline
    case character
    case dedicatedTransport
    case infantry
    case vehicle
    case mounted

    var id: String { rawValue }

    var title: String {
        switch self {
        case .all: return "All types"
        case .battleline: return "Battleline"
        case .character: return "Characters"
        case .dedicatedTransport: return "Dedicated transports"
        case .infantry: return "Infantry"
        case .vehicle: return "Vehicles"
        case .mounted: return "Mounted"
        }
    }
}

enum ArmyListUnitPickerFiltering {
    static func sheets(
        from catalog: ArmyCatalog,
        factionID: String,
        query: String,
        includeLegends: Bool,
        typeFilter: ArmyListUnitTypeFilter
    ) -> [DatasheetDefinition] {
        catalog.datasheets
            .filter { $0.factionID == factionID }
            .filter { includeLegends || !$0.legends }
            .filter { matchesType($0, filter: typeFilter) }
            .filter {
                query.isEmpty
                    || $0.name.localizedCaseInsensitiveContains(query)
                    || $0.keywords.contains { $0.localizedCaseInsensitiveContains(query) }
            }
            .sorted { $0.name.localizedCaseInsensitiveCompare($1.name) == .orderedAscending }
    }

    static func matchesType(_ sheet: DatasheetDefinition, filter: ArmyListUnitTypeFilter) -> Bool {
        switch filter {
        case .all:
            return true
        case .battleline:
            return sheet.battleline
        case .character:
            return sheet.characterRole != nil
        case .dedicatedTransport:
            return sheet.dedicatedTransport
        case .infantry:
            return sheet.keywords.contains("Infantry")
        case .vehicle:
            return sheet.keywords.contains("Vehicle")
        case .mounted:
            return sheet.keywords.contains("Mounted")
        }
    }
}

struct ArmyListUnitDetailView: View {
    @Binding var list: ArmyListDocument
    let unitID: UUID
    let catalog: ArmyCatalog

    private var index: Int? {
        list.units.firstIndex { $0.id == unitID }
    }

    var body: some View {
        Group {
            if let index, let sheet = catalog.datasheet(id: list.units[index].datasheetID) {
                Form {
                    Section(sheet.name) {
                        Picker("Models", selection: $list.units[index].models) {
                            ForEach(sheet.modelCounts, id: \.self) { count in
                                Text("\(count)").tag(count)
                            }
                        }
                        .accessibilityIdentifier("armyListUnitModelsPicker")
                    }

                    if sheet.characterRole != nil {
                        Section("Attachment") {
                            Picker("Joined to", selection: $list.units[index].attachedToUnitID) {
                                Text("None (independent)").tag(UUID?.none)
                                ForEach(attachTargets(for: sheet, excluding: unitID)) { target in
                                    Text(catalog.datasheet(id: target.datasheetID)?.name ?? target.datasheetID)
                                        .tag(Optional(target.id))
                                }
                            }
                            .accessibilityIdentifier("armyListUnitAttachPicker")
                        }
                    }

                    if !sheet.optionGroups.isEmpty {
                        Section("Loadout") {
                            ForEach(sheet.optionGroups) { group in
                                optionGroupControl(unitIndex: index, group: group)
                            }
                        }
                    }

                    let available = availableEnhancements(for: sheet)
                    if !available.isEmpty {
                        Section("Enhancements") {
                            ForEach(available, id: \.enhancement.id) { item in
                                Toggle(isOn: enhancementBinding(unitIndex: index, enhancementID: item.enhancement.id)) {
                                    VStack(alignment: .leading, spacing: 2) {
                                        Text(item.enhancement.name)
                                        Text("\(item.enhancement.points) pts · \(item.detachment.name)\(item.enhancement.isUpgrade ? " · Upgrade" : "")")
                                            .font(.caption)
                                            .foregroundStyle(.secondary)
                                    }
                                }
                                .accessibilityIdentifier("armyListEnhancement-\(item.enhancement.id)")
                            }
                        }
                    }
                }
                .navigationTitle(sheet.name)
                .onAppear {
                    seedDefaultOptionsIfNeeded(unitIndex: index, sheet: sheet)
                }
            } else {
                VStack(spacing: 8) {
                    Image(systemName: "questionmark.circle")
                        .font(.largeTitle)
                        .foregroundStyle(.secondary)
                    Text("Unit missing")
                        .font(.headline)
                }
                .frame(maxWidth: .infinity, maxHeight: .infinity)
            }
        }
    }

    private func attachTargets(for sheet: DatasheetDefinition, excluding: UUID) -> [ListUnitInstance] {
        list.units.filter { unit in
            guard unit.id != excluding else { return false }
            let body = catalog.datasheet(id: unit.datasheetID)
            guard body?.characterRole == nil else { return false }
            if sheet.leaderTo.isEmpty { return true }
            return sheet.leaderTo.contains(unit.datasheetID)
        }
    }

    private func availableEnhancements(
        for sheet: DatasheetDefinition
    ) -> [(detachment: DetachmentDefinition, enhancement: EnhancementDefinition)] {
        var result: [(DetachmentDefinition, EnhancementDefinition)] = []
        for detachmentID in list.detachmentIDs {
            guard let detachment = catalog.detachment(id: detachmentID) else { continue }
            for enhancement in detachment.enhancements {
                if enhancement.isUpgrade {
                    if sheet.characterRole == nil {
                        result.append((detachment, enhancement))
                    }
                } else if sheet.characterRole != nil {
                    result.append((detachment, enhancement))
                }
            }
        }
        return result
    }

    private func enhancementBinding(unitIndex: Int, enhancementID: String) -> Binding<Bool> {
        Binding(
            get: { list.units[unitIndex].enhancementIDs.contains(enhancementID) },
            set: { enabled in
                if enabled {
                    list.units[unitIndex].enhancementIDs = [enhancementID]
                } else {
                    list.units[unitIndex].enhancementIDs.removeAll { $0 == enhancementID }
                }
            }
        )
    }

    @ViewBuilder
    private func optionGroupControl(unitIndex: Int, group: OptionGroupDefinition) -> some View {
        if group.min == 0, group.max == 1, group.options.count == 1 {
            let option = group.options[0]
            Toggle(isOn: optionToggleBinding(unitIndex: unitIndex, group: group, optionID: option.id)) {
                optionLabel(option)
            }
            .accessibilityIdentifier("armyListOption-\(option.id)")
        } else if group.max == 1 {
            Picker(selection: exclusiveOptionBinding(unitIndex: unitIndex, group: group)) {
                if group.min == 0 {
                    Text("None").tag(String?.none)
                }
                ForEach(group.options) { option in
                    optionLabel(option).tag(Optional(option.id))
                }
            } label: {
                Text(group.name)
            }
            .accessibilityIdentifier("armyListOptionGroup-\(group.id)")
        } else {
            // Rare multi-pick groups: toggles capped at max.
            ForEach(group.options) { option in
                Toggle(isOn: optionToggleBinding(unitIndex: unitIndex, group: group, optionID: option.id)) {
                    optionLabel(option)
                }
                .accessibilityIdentifier("armyListOption-\(option.id)")
            }
        }
    }

    private func optionLabel(_ option: OptionDefinition) -> some View {
        VStack(alignment: .leading, spacing: 2) {
            Text(option.name)
            if option.points != 0 {
                Text("\(option.points) pts")
                    .font(.caption)
                    .foregroundStyle(.secondary)
            }
        }
    }

    private func exclusiveOptionBinding(
        unitIndex: Int,
        group: OptionGroupDefinition
    ) -> Binding<String?> {
        let groupIDs = Set(group.options.map(\.id))
        return Binding(
            get: {
                list.units[unitIndex].optionIDs.first { groupIDs.contains($0) }
            },
            set: { newValue in
                list.units[unitIndex].optionIDs.removeAll { groupIDs.contains($0) }
                if let newValue {
                    list.units[unitIndex].optionIDs.append(newValue)
                }
            }
        )
    }

    private func optionToggleBinding(
        unitIndex: Int,
        group: OptionGroupDefinition,
        optionID: String
    ) -> Binding<Bool> {
        let groupIDs = Set(group.options.map(\.id))
        return Binding(
            get: { list.units[unitIndex].optionIDs.contains(optionID) },
            set: { enabled in
                if enabled {
                    var selected = list.units[unitIndex].optionIDs.filter { groupIDs.contains($0) }
                    if !selected.contains(optionID) {
                        selected.append(optionID)
                    }
                    if selected.count > group.max {
                        selected = Array(selected.suffix(group.max))
                    }
                    list.units[unitIndex].optionIDs.removeAll { groupIDs.contains($0) }
                    list.units[unitIndex].optionIDs.append(contentsOf: selected)
                } else {
                    list.units[unitIndex].optionIDs.removeAll { $0 == optionID }
                }
            }
        )
    }

    private func seedDefaultOptionsIfNeeded(unitIndex: Int, sheet: DatasheetDefinition) {
        guard list.units[unitIndex].optionIDs.isEmpty else { return }
        let defaults = sheet.defaultOptionIDs()
        guard !defaults.isEmpty else { return }
        list.units[unitIndex].optionIDs = defaults
    }
}

private struct ShareArmyListSheet: View {
    let text: String
    let fileURL: URL?

    var body: some View {
        NavigationStack {
            List {
                Section("Plain text") {
                    ShareLink(item: text) {
                        Label("Share roster text", systemImage: "doc.plaintext")
                    }
                    .accessibilityIdentifier("armyListShareText")
                }
                if let fileURL {
                    Section("JSON") {
                        ShareLink(item: fileURL) {
                            Label("Share .army.json", systemImage: "doc")
                        }
                        .accessibilityIdentifier("armyListShareJSON")
                    }
                }
                Section("Preview") {
                    Text(text)
                        .font(.footnote.monospaced())
                        .textSelection(.enabled)
                }
            }
            .navigationTitle("Share")
            .navigationBarTitleDisplayMode(.inline)
        }
    }
}
