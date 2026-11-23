import Foundation
import Network
import SwiftUI

/// Central `@MainActor` orchestrator for Lantern's continuous Watch → Score → Explain loop.
@MainActor
final class SentinelController: ObservableObject {
    @Published private(set) var currentNetwork: NetworkIdentity = .offline
    @Published private(set) var currentTrust: NetworkTrust = .unknown
    @Published private(set) var devices: [LANDevice] = []
    @Published private(set) var upnpMappings: [UPnPMapping] = []
    @Published private(set) var hostProcesses: [ProcessNetworkSnapshot] = []
    @Published private(set) var connectivity: ConnectivityHealth = .unknown
    @Published private(set) var externalVantage: ExternalVantageSnapshot?
    @Published private(set) var findings: [Finding] = []
    @Published private(set) var muteRules: [MuteRule] = []
    @Published private(set) var isScanning = false
    @Published private(set) var lastScanAt: Date?
    @Published private(set) var afmAvailability: FoundationModelsAvailability = .evaluate()

    @Published var scanIntervalSeconds: Int = 60
    @Published var notificationsEnabled: Bool = true
    @Published var externalVantageConfig: ExternalVantageConfig = ExternalVantageConfig()

    let store: BaselineStore

    private let pathMonitor = NWPathMonitor()
    private let pathQueue = DispatchQueue(label: "io.github.imjasonh.lantern.path", qos: .utility)
    private var pathSatisfied = true
    private var watchTask: Task<Void, Never>?
    private let notificationCooldownSeconds: TimeInterval = 3600

    init(store: BaselineStore = BaselineStore(), autoStart: Bool = true) {
        self.store = store
        let persisted = store.state
        self.findings = persisted.findings
        self.muteRules = persisted.muteRules
        self.scanIntervalSeconds = max(15, persisted.scanIntervalSeconds)
        self.notificationsEnabled = persisted.notificationsEnabled
        self.externalVantageConfig = persisted.externalVantage

        if autoStart {
            start()
        }
    }

    deinit {
        pathMonitor.cancel()
        watchTask?.cancel()
    }

    // MARK: - Derived UI state

    var activeFindings: [Finding] {
        findings
            .filter { !$0.isAcknowledged }
            .sorted { lhs, rhs in
                if lhs.severity != rhs.severity { return lhs.severity > rhs.severity }
                return lhs.lastSeen > rhs.lastSeen
            }
    }

    var highestActiveSeverity: FindingSeverity? {
        activeFindings.map(\.severity).max()
    }

    var menuBarSymbol: String {
        if !connectivity.isPathSatisfied {
            return "wifi.exclamationmark"
        }
        switch highestActiveSeverity {
        case .critical:
            return "shield.slash.fill"
        case .warning:
            return "exclamationmark.shield.fill"
        case .notice:
            return "flame.fill"
        case .info, .none:
            return "lantern.fill" // Falls back gracefully below via symbolExists helper
        }
    }

    /// SF Symbol guaranteed to exist on macOS 14+.
    var safeMenuBarSymbol: String {
        if !connectivity.isPathSatisfied {
            return "wifi.exclamationmark"
        }
        switch highestActiveSeverity {
        case .critical:
            return "exclamationmark.shield.fill"
        case .warning:
            return "exclamationmark.triangle.fill"
        case .notice:
            return "bell.badge.fill"
        case .info, .none:
            return "lightbulb.max.fill"
        }
    }

    // MARK: - Lifecycle

    func start() {
        NotificationManager.requestPermissionIfNeeded()

        pathMonitor.pathUpdateHandler = { [weak self] path in
            let satisfied = (path.status == .satisfied)
            Task { @MainActor [weak self] in
                guard let self else { return }
                let changed = (self.pathSatisfied != satisfied)
                self.pathSatisfied = satisfied
                if changed {
                    await self.runScan(runActiveConnectivityProbes: true)
                }
            }
        }
        pathMonitor.start(queue: pathQueue)

        watchTask?.cancel()
        watchTask = Task { [weak self] in
            while let self, !Task.isCancelled {
                await self.runScan(runActiveConnectivityProbes: false)
                let delay = UInt64(max(15, self.scanIntervalSeconds)) * 1_000_000_000
                try? await Task.sleep(nanoseconds: delay)
            }
        }
    }

    // MARK: - Scan pipeline (Watch → Score → Explain)

    func runScan(runActiveConnectivityProbes: Bool = true) async {
        guard !isScanning else { return }
        isScanning = true
        defer { isScanning = false }

        afmAvailability = FoundationModelsAvailability.evaluate()
        let now = Date()

        // Stage 1: Collect
        let network = await Task.detached(priority: .utility) {
            NetworkIdentityCollector.collect()
        }.value

        let baseline = store.baseline(for: network, now: now)
        currentNetwork = network
        currentTrust = baseline.trust

        // Background discovery stays strictly passive (OS ARP table + mDNS browse).
        // Active subnet nudges and TCP port probes only happen on explicit user clicks.
        async let discoveredTask = LANDiscoveryCollector.discover(
            network: network,
            existingDevices: baseline.knownDevices,
            nudgeSubnet: false,
            now: now
        )
        async let upnpTask: [UPnPMapping] = (network != .offline && baseline.trust != .untrusted)
            ? UPnPCollector.collect()
            : []
        async let hostTask = Task.detached(priority: .utility) {
            HostTrafficCollector.collect()
        }.value
        async let connTask = ConnectivityCollector.collect(
            pathSatisfied: pathSatisfied,
            network: network,
            runActiveProbes: runActiveConnectivityProbes,
            now: now
        )
        async let externalTask = ExternalVantageCollector.collect(
            config: externalVantageConfig,
            now: now
        )

        let discovered = await discoveredTask
        let mappings = await upnpTask
        let processes = await hostTask
        let conn = await connTask
        let external = await externalTask

        let snapshot = WatchSnapshot(
            capturedAt: now,
            network: network,
            devices: discovered,
            upnpMappings: mappings,
            hostProcesses: processes,
            connectivity: conn,
            externalVantage: external
        )

        // Stage 2: Score deterministically
        var thresholds = AnomalyDetector.Thresholds()
        thresholds.chattyDNSQueries = max(500, externalVantageConfig.chattyQueryThreshold)

        let evaluation = AnomalyDetector.evaluate(
            snapshot: snapshot,
            baseline: baseline,
            muteRules: store.state.muteRules,
            thresholds: thresholds
        )

        var newlyCreatedFindings: [Finding] = []
        store.update { state in
            state.baselines[network.id] = evaluation.updatedBaseline

            for candidate in evaluation.emittedFindings {
                if let existingIdx = state.findings.firstIndex(where: {
                    $0.networkID == candidate.networkID && $0.dedupeKey == candidate.dedupeKey
                }) {
                    state.findings[existingIdx].lastSeen = now
                    state.findings[existingIdx].evidence = candidate.evidence
                    state.findings[existingIdx].summary = candidate.summary
                } else {
                    state.findings.insert(candidate, at: 0)
                    newlyCreatedFindings.append(candidate)
                }
            }

            // Cap stored history at 100 findings.
            if state.findings.count > 100 {
                state.findings = Array(state.findings.prefix(100))
            }
        }

        // Publish live state
        devices = evaluation.updatedBaseline.knownDevices.values.sorted { lhs, rhs in
            if lhs.isGateway != rhs.isGateway { return lhs.isGateway }
            if lhs.isThisMac != rhs.isThisMac { return lhs.isThisMac }
            return lhs.ipAddress.localizedStandardCompare(rhs.ipAddress) == .orderedAscending
        }
        upnpMappings = mappings
        hostProcesses = processes
        connectivity = conn
        externalVantage = external
        findings = store.state.findings
        muteRules = store.state.muteRules
        lastScanAt = now

        // Stage 3: Narrow AFM enrichment (runs asynchronously, zero-tool, tiny context)
        let unclassified = devices.filter { $0.classification == nil }.prefix(3)
        for device in unclassified {
            let netID = network.id
            Task { [weak self] in
                let label = await DeviceClassifier.classify(device)
                guard let self else { return }
                self.store.setDeviceClassification(label, mac: device.id, networkID: netID)
                if let idx = self.devices.firstIndex(where: { $0.id == device.id }) {
                    self.devices[idx].classification = label
                }
            }
        }

        for finding in newlyCreatedFindings {
            Task { [weak self] in
                let explanation = await FindingExplainer.explain(finding)
                guard let self else { return }
                self.attachExplanation(explanation, toFindingID: finding.id)
                self.notifyIfAppropriate(findingID: finding.id)
            }
        }
    }

    // MARK: - User Actions

    func setNetworkTrust(_ trust: NetworkTrust) {
        currentTrust = trust
        store.setTrust(trust, for: currentNetwork.id)
    }

    func acknowledge(finding: Finding) {
        store.update { state in
            if let idx = state.findings.firstIndex(where: { $0.id == finding.id }) {
                state.findings[idx].isAcknowledged = true
            }
        }
        findings = store.state.findings
    }

    func acknowledgeAll() {
        store.update { state in
            for idx in state.findings.indices {
                state.findings[idx].isAcknowledged = true
            }
        }
        findings = store.state.findings
    }

    func mute(finding: Finding) {
        store.mute(finding: finding)
        findings = store.state.findings
        muteRules = store.state.muteRules
    }

    func removeMuteRule(id: UUID) {
        store.removeMuteRule(id: id)
        muteRules = store.state.muteRules
    }

    func trust(device: LANDevice, trusted: Bool = true) {
        store.trustDevice(mac: device.id, networkID: currentNetwork.id, trusted: trusted)
        if let idx = devices.firstIndex(where: { $0.id == device.id }) {
            devices[idx].isTrusted = trusted
        }
        if trusted {
            // Acknowledge any open new-device findings for this MAC.
            store.update { state in
                for idx in state.findings.indices
                    where state.findings[idx].subjectID == device.id
                        && state.findings[idx].kind == .newDevice
                {
                    state.findings[idx].isAcknowledged = true
                }
            }
            findings = store.state.findings
        }
    }

    func trustProcess(_ processName: String) {
        store.trustProcess(processName, networkID: currentNetwork.id)
        store.update { state in
            for idx in state.findings.indices where state.findings[idx].subjectID == processName {
                state.findings[idx].isAcknowledged = true
            }
        }
        findings = store.state.findings
    }

    /// Persists open ports discovered from an explicit user-clicked probe in `DeviceExplorerSheet`.
    func recordInteractivePortProbe(deviceID: String, openPorts: [OpenPort]) {
        let netID = currentNetwork.id
        store.update { state in
            guard var baseline = state.baselines[netID],
                  var device = baseline.knownDevices[deviceID]
            else { return }
            device.openPorts = openPorts
            baseline.knownDevices[deviceID] = device
            state.baselines[netID] = baseline
        }
        if let idx = devices.firstIndex(where: { $0.id == deviceID }) {
            devices[idx].openPorts = openPorts
        }
    }

    func updateDeviceClassification(deviceID: String, classification: DeviceClassification) {
        store.setDeviceClassification(classification, mac: deviceID, networkID: currentNetwork.id)
        if let idx = devices.firstIndex(where: { $0.id == deviceID }) {
            devices[idx].classification = classification
        }
    }

    func saveSettings() {
        let interval = max(15, scanIntervalSeconds)
        scanIntervalSeconds = interval
        store.update { state in
            state.scanIntervalSeconds = interval
            state.notificationsEnabled = notificationsEnabled
            state.externalVantage = externalVantageConfig
        }
    }

    // MARK: - Private helpers

    private func attachExplanation(_ explanation: FindingExplanation, toFindingID id: UUID) {
        store.update { state in
            if let idx = state.findings.firstIndex(where: { $0.id == id }) {
                state.findings[idx].explanation = explanation
            }
        }
        findings = store.state.findings
    }

    private func notifyIfAppropriate(findingID: UUID) {
        guard notificationsEnabled else { return }
        guard currentTrust == .trusted else { return }
        guard let finding = findings.first(where: { $0.id == findingID }) else { return }
        guard finding.severity >= .warning else { return }

        let now = Date()
        let shouldPost = store.update { state -> Bool in
            if let last = state.lastNotifiedByKey[finding.dedupeKey],
               now.timeIntervalSince(last) < notificationCooldownSeconds
            {
                return false
            }
            state.lastNotifiedByKey[finding.dedupeKey] = now
            return true
        }
        if shouldPost {
            NotificationManager.post(finding: finding)
        }
    }
}
