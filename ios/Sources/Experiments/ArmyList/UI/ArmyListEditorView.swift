import SwiftUI

/// Authoring surface: detachments, units, live validation, share.
struct ArmyListEditorView: View {
    @State private var list: ArmyListDocument
    let catalog: ArmyCatalog
    let store: ArmyListStore
    var onChange: () -> Void

    @State private var showAddUnit = false
    @State private var showShare = false
    @State private var shareText = ""
    @State private var shareFileURL: URL?

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
                }
                .onDelete(perform: deleteUnits)

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
                Button {
                    prepareShare()
                    showShare = true
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
                    list.units.append(ListUnitInstance(datasheetID: sheet.id, models: models))
                    showAddUnit = false
                    persist()
                }
            }
        }
        .sheet(isPresented: $showShare) {
            ShareArmyListSheet(text: shareText, fileURL: shareFileURL)
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
                Text("\(result.errors.count) errors · \(result.warnings.count) warnings")
                    .font(.caption)
                    .foregroundStyle(.secondary)
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

    private func deleteUnits(at offsets: IndexSet) {
        let removedIDs = Set(offsets.map { list.units[$0].id })
        list.units.remove(atOffsets: offsets)
        list.units = list.units.map { unit in
            var copy = unit
            if let attached = copy.attachedToUnitID, removedIDs.contains(attached) {
                copy.attachedToUnitID = nil
            }
            return copy
        }
        if let warlord = list.warlordUnitID, removedIDs.contains(warlord) {
            list.warlordUnitID = nil
        }
    }

    private func persist() {
        try? store.save(list)
        onChange()
    }

    private func prepareShare() {
        let result = validation
        shareText = ArmyListTextExporter.text(for: list, catalog: catalog, validation: result)
        if let data = try? ArmyListJSONExporter.data(for: list, validation: result) {
            let url = FileManager.default.temporaryDirectory
                .appendingPathComponent(ArmyListJSONExporter.filename(for: list))
            try? data.write(to: url, options: .atomic)
            shareFileURL = url
        }
    }
}

struct ArmyListUnitPickerView: View {
    let catalog: ArmyCatalog
    let factionID: String
    var onPick: (DatasheetDefinition) -> Void

    @Environment(\.dismiss) private var dismiss
    @State private var query = ""

    private var sheets: [DatasheetDefinition] {
        catalog.datasheets
            .filter { $0.factionID == factionID }
            .filter {
                query.isEmpty
                    || $0.name.localizedCaseInsensitiveContains(query)
                    || $0.keywords.contains { $0.localizedCaseInsensitiveContains(query) }
            }
            .sorted { $0.name.localizedCaseInsensitiveCompare($1.name) == .orderedAscending }
    }

    var body: some View {
        List(sheets) { sheet in
            Button {
                onPick(sheet)
            } label: {
                VStack(alignment: .leading, spacing: 2) {
                    Text(sheet.name)
                        .foregroundStyle(.primary)
                    HStack(spacing: 6) {
                        if sheet.battleline {
                            Text("Battleline")
                        }
                        if sheet.characterRole != nil {
                            Text("Character")
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
        .searchable(text: $query, prompt: "Datasheets")
        .navigationTitle("Add unit")
        .navigationBarTitleDisplayMode(.inline)
        .toolbar {
            ToolbarItem(placement: .cancellationAction) {
                Button("Cancel") { dismiss() }
            }
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

                    Section("Enhancements") {
                        let available = availableEnhancements(for: sheet)
                        if available.isEmpty {
                            Text("Select a detachment that grants enhancements, or this unit cannot take any.")
                                .font(.footnote)
                                .foregroundStyle(.secondary)
                        } else {
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
