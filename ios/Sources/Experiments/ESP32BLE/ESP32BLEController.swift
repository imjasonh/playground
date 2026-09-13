import Combine
@preconcurrency import CoreBluetooth
import Foundation

/// A nearby advertisement for the Playground BLE service.
struct ESP32BLEAdvertisement: Identifiable, Equatable {
    let id: UUID
    var name: String
    var rssi: Int
}

/// Drives Core Bluetooth as a central for the `esp32-ble` firmware.
///
/// `CBCentralManager` uses the main queue (`queue: nil`) so delegate callbacks
/// land on the same actor as the published UI state.
@MainActor
final class ESP32BLEController: NSObject, ObservableObject {
    enum Phase: String {
        case idle
        case scanning
        case connecting
        case connected
    }

    @Published var bluetoothState: CBManagerState = .unknown
    @Published var phase: Phase = .idle
    @Published var devices: [ESP32BLEAdvertisement] = []
    @Published var connectedName = ""
    @Published var status: ESP32BLEStatus?
    @Published var statusLog: [String] = []
    @Published var commandDraft = "blink every 1s"
    @Published var blinkPeriodMs = Double(ESP32BLEProtocol.sliderDefaultBlinkMs)
    @Published var statusMessage = "Flash esp32-ble, then scan."

    private var central: CBCentralManager?
    private var peripherals: [UUID: CBPeripheral] = [:]
    private var connectedPeripheral: CBPeripheral?
    private var commandCharacteristic: CBCharacteristic?
    private var statusCharacteristic: CBCharacteristic?
    private var blinkSendTask: Task<Void, Never>?
    private var isAdjustingBlinkSlider = false
    private var preferred: ESP32BLEPreferredDevice?
    private var wantsReconnect = false
    private let defaults: UserDefaults

    private let serviceUUID = CBUUID(string: ESP32BLEProtocol.serviceUUIDString)
    private let commandUUID = CBUUID(string: ESP32BLEProtocol.commandUUIDString)
    private let statusUUID = CBUUID(string: ESP32BLEProtocol.statusUUIDString)

    init(defaults: UserDefaults = .standard) {
        self.defaults = defaults
        super.init()
        preferred = ESP32BLEPreferredDevice.load(from: defaults)
    }

    var isBluetoothUsable: Bool {
        bluetoothState == .poweredOn
    }

    var availabilitySummary: String {
        switch bluetoothState {
        case .poweredOn:
            return "Bluetooth is on."
        case .poweredOff:
            return "Turn on Bluetooth to scan."
        case .unauthorized:
            return "Allow Bluetooth in Settings to scan for the ESP32."
        case .unsupported:
            return "BLE needs a physical iPhone. The Simulator cannot talk to an ESP32."
        case .resetting:
            return "Bluetooth is resetting."
        case .unknown:
            return "Waiting for Bluetooth."
        @unknown default:
            return "Bluetooth is unavailable."
        }
    }

    func start() {
        preferred = ESP32BLEPreferredDevice.load(from: defaults)
        wantsReconnect = preferred != nil
        if central == nil {
            central = CBCentralManager(delegate: self, queue: nil)
        }
        applyBluetoothState(central?.state ?? .unknown)
    }

    func stop() {
        blinkSendTask?.cancel()
        wantsReconnect = false
        cancelPendingConnection()
        central?.stopScan()
        phase = .idle
        devices = []
        peripherals.removeAll()
    }

    func startScan() {
        guard let central, central.state == .poweredOn else {
            statusMessage = availabilitySummary
            return
        }
        if connectedPeripheral != nil {
            cancelPendingConnection()
        }
        devices = []
        let kept = preferred.flatMap { peripherals[$0.id] }
        peripherals.removeAll()
        if let kept {
            peripherals[kept.identifier] = kept
        }
        beginDiscoveryScan()
        if wantsReconnect {
            attemptPreferredConnect()
        }
    }

    func connect(to advertisement: ESP32BLEAdvertisement) {
        guard let peripheral = peripherals[advertisement.id] else {
            statusMessage = "That device is no longer in range. Scan again."
            return
        }
        rememberPreferred(id: advertisement.id, name: advertisement.name)
        wantsReconnect = true
        connect(peripheral, name: advertisement.name, reconnecting: false)
    }

    func disconnect() {
        wantsReconnect = false
        blinkSendTask?.cancel()
        cancelPendingConnection()
        phase = .idle
        statusMessage = "Disconnected."
    }

    func send(_ command: ESP32BLECommand) {
        sendRaw(ESP32BLEProtocol.encode(command))
    }

    func updateBlinkPeriodMs(_ raw: Double) {
        blinkPeriodMs = Double(ESP32BLEProtocol.clampSliderPeriodMs(raw))
        scheduleBlinkSend()
    }

    func blinkSliderEditingChanged(_ editing: Bool) {
        isAdjustingBlinkSlider = editing
        if !editing {
            flushBlinkSend()
        }
    }

    func sendDraft() {
        let raw = commandDraft.trimmingCharacters(in: .whitespacesAndNewlines)
        if raw.isEmpty {
            statusMessage = "Type a command first."
            return
        }
        sendRaw(raw)
    }

    private func scheduleBlinkSend() {
        blinkSendTask?.cancel()
        blinkSendTask = Task { @MainActor [weak self] in
            try? await Task.sleep(for: .milliseconds(180))
            guard let self, !Task.isCancelled else {
                return
            }
            self.send(.blink(periodMs: UInt32(self.blinkPeriodMs)))
        }
    }

    private func flushBlinkSend() {
        blinkSendTask?.cancel()
        blinkSendTask = nil
        send(.blink(periodMs: UInt32(blinkPeriodMs)))
    }

    private func adoptStatus(_ parsed: ESP32BLEStatus?) {
        status = parsed
        guard !isAdjustingBlinkSlider, let parsed, parsed.blinkMs > 0 else {
            return
        }
        if parsed.blinkMs >= ESP32BLEProtocol.sliderMinBlinkMs,
           parsed.blinkMs <= ESP32BLEProtocol.sliderMaxBlinkMs
        {
            blinkPeriodMs = Double(parsed.blinkMs)
        }
    }

    private func sendRaw(_ raw: String) {
        guard let peripheral = connectedPeripheral, let characteristic = commandCharacteristic else {
            statusMessage = "Connect to a device before sending a command."
            return
        }
        guard let data = raw.data(using: .utf8) else {
            statusMessage = "Could not encode that command as UTF-8."
            return
        }
        peripheral.writeValue(data, for: characteristic, type: .withResponse)
        statusMessage = "Sent \(raw)"
    }

    private func applyBluetoothState(_ state: CBManagerState) {
        bluetoothState = state
        if state != .poweredOn {
            central?.stopScan()
            if phase == .scanning {
                phase = .idle
            }
            if phase == .idle || phase == .scanning {
                statusMessage = availabilitySummary
            }
            return
        }
        if phase == .connected {
            return
        }
        if wantsReconnect {
            attemptPreferredConnect()
            beginDiscoveryScan()
            return
        }
        if phase == .idle {
            startScan()
        }
    }

    private func rememberPreferred(id: UUID, name: String) {
        let next = ESP32BLEPreferredDevice(id: id, name: name)
        preferred = next
        next.save(to: defaults)
    }

    private func connect(_ peripheral: CBPeripheral, name: String, reconnecting: Bool) {
        guard let central, central.state == .poweredOn else {
            statusMessage = availabilitySummary
            return
        }
        peripherals[peripheral.identifier] = peripheral
        connectedPeripheral = peripheral
        connectedName = name
        peripheral.delegate = self
        phase = .connecting
        statusMessage = reconnecting
            ? "Reconnecting to \(name)."
            : "Connecting to \(name)."
        central.connect(peripheral, options: nil)
    }

    private func attemptPreferredConnect() {
        guard wantsReconnect, let preferred, let central, central.state == .poweredOn else {
            return
        }
        if connectedPeripheral?.identifier == preferred.id,
           phase == .connected || phase == .connecting
        {
            return
        }
        let already = central.retrieveConnectedPeripherals(withServices: [serviceUUID])
        if let match = already.first(where: { $0.identifier == preferred.id }) {
            connect(match, name: preferred.name, reconnecting: true)
            return
        }
        if let match = central.retrievePeripherals(withIdentifiers: [preferred.id]).first {
            connect(match, name: preferred.name, reconnecting: true)
        }
    }

    private func beginDiscoveryScan() {
        guard let central, central.state == .poweredOn else {
            return
        }
        if phase == .idle {
            phase = .scanning
        }
        if phase == .scanning {
            statusMessage = wantsReconnect
                ? "Reconnecting to \(preferred?.name ?? ESP32BLEProtocol.deviceName)."
                : "Scanning for \(ESP32BLEProtocol.deviceName)."
        }
        central.scanForPeripherals(
            withServices: [serviceUUID],
            options: [CBCentralManagerScanOptionAllowDuplicatesKey: true]
        )
    }

    private func handleUnexpectedDrop(of peripheral: CBPeripheral, message: String) {
        blinkSendTask?.cancel()
        commandCharacteristic = nil
        statusCharacteristic = nil
        connectedPeripheral = nil
        status = nil
        peripherals[peripheral.identifier] = peripheral
        guard wantsReconnect, peripheral.identifier == preferred?.id else {
            connectedName = ""
            phase = .idle
            statusMessage = message
            return
        }
        connect(peripheral, name: preferred?.name ?? connectedName, reconnecting: true)
        beginDiscoveryScan()
    }

    private func cancelPendingConnection() {
        if let central, let peripheral = connectedPeripheral {
            central.cancelPeripheralConnection(peripheral)
        }
        connectedPeripheral = nil
        commandCharacteristic = nil
        statusCharacteristic = nil
        connectedName = ""
        status = nil
    }

    private func sortDevices() {
        let preferredID = preferred?.id
        devices.sort { a, b in
            if a.id == preferredID { return true }
            if b.id == preferredID { return false }
            return a.rssi > b.rssi
        }
    }

    private func recordStatusLine(_ line: String) {
        statusLog.insert(line, at: 0)
        if statusLog.count > 20 {
            statusLog = Array(statusLog.prefix(20))
        }
    }
}

extension ESP32BLEController: CBCentralManagerDelegate {
    nonisolated func centralManagerDidUpdateState(_ central: CBCentralManager) {
        let state = central.state
        Task { @MainActor in
            self.applyBluetoothState(state)
        }
    }

    nonisolated func centralManager(
        _ central: CBCentralManager,
        didDiscover peripheral: CBPeripheral,
        advertisementData: [String: Any],
        rssi RSSI: NSNumber
    ) {
        let id = peripheral.identifier
        let advertisedName = advertisementData[CBAdvertisementDataLocalNameKey] as? String
        let name = advertisedName
            ?? peripheral.name
            ?? ESP32BLEProtocol.deviceName
        let rssi = RSSI.intValue
        Task { @MainActor in
            self.peripherals[id] = peripheral
            let row = ESP32BLEAdvertisement(id: id, name: name, rssi: rssi)
            if let index = self.devices.firstIndex(where: { $0.id == id }) {
                self.devices[index] = row
            } else {
                self.devices.append(row)
            }
            self.sortDevices()
            if ESP32BLEPreferredDevice.shouldReconnect(
                discovered: id,
                preferred: self.preferred?.id,
                wantsReconnect: self.wantsReconnect,
                isBusy: self.phase == .connected || self.phase == .connecting
            ) {
                let label = self.preferred?.name ?? name
                self.connect(peripheral, name: label, reconnecting: true)
            }
        }
    }

    nonisolated func centralManager(_ central: CBCentralManager, didConnect peripheral: CBPeripheral) {
        let service = CBUUID(string: ESP32BLEProtocol.serviceUUIDString)
        Task { @MainActor in
            self.central?.stopScan()
            self.phase = .connected
            self.connectedPeripheral = peripheral
            self.connectedName = self.preferred?.name ?? peripheral.name ?? ESP32BLEProtocol.deviceName
            self.rememberPreferred(id: peripheral.identifier, name: self.connectedName)
            self.wantsReconnect = true
            self.statusMessage = "Connected. Discovering services."
        }
        peripheral.discoverServices([service])
    }

    nonisolated func centralManager(
        _ central: CBCentralManager,
        didFailToConnect peripheral: CBPeripheral,
        error: Error?
    ) {
        let detail = error?.localizedDescription ?? "unknown error"
        Task { @MainActor in
            self.handleUnexpectedDrop(of: peripheral, message: "Connect failed: \(detail)")
        }
    }

    nonisolated func centralManager(
        _ central: CBCentralManager,
        didDisconnectPeripheral peripheral: CBPeripheral,
        error: Error?
    ) {
        let detail = error?.localizedDescription
        Task { @MainActor in
            if self.wantsReconnect {
                self.handleUnexpectedDrop(
                    of: peripheral,
                    message: "Reconnecting to \(self.preferred?.name ?? ESP32BLEProtocol.deviceName)."
                )
                return
            }
            self.connectedPeripheral = nil
            self.commandCharacteristic = nil
            self.statusCharacteristic = nil
            self.connectedName = ""
            self.status = nil
            self.phase = .idle
            if let detail {
                self.statusMessage = "Disconnected: \(detail)"
            } else {
                self.statusMessage = "Disconnected."
            }
        }
    }
}

extension ESP32BLEController: CBPeripheralDelegate {
    nonisolated func peripheral(_ peripheral: CBPeripheral, didDiscoverServices error: Error?) {
        if let error {
            Task { @MainActor in
                self.statusMessage = "Service discovery failed: \(error.localizedDescription)"
            }
            return
        }
        let serviceUUID = CBUUID(string: ESP32BLEProtocol.serviceUUIDString)
        let commandUUID = CBUUID(string: ESP32BLEProtocol.commandUUIDString)
        let statusUUID = CBUUID(string: ESP32BLEProtocol.statusUUIDString)
        guard let services = peripheral.services else {
            return
        }
        for service in services where service.uuid == serviceUUID {
            peripheral.discoverCharacteristics([commandUUID, statusUUID], for: service)
        }
    }

    nonisolated func peripheral(
        _ peripheral: CBPeripheral,
        didDiscoverCharacteristicsFor service: CBService,
        error: Error?
    ) {
        if let error {
            Task { @MainActor in
                self.statusMessage = "Characteristic discovery failed: \(error.localizedDescription)"
            }
            return
        }
        let commandUUID = CBUUID(string: ESP32BLEProtocol.commandUUIDString)
        let statusUUID = CBUUID(string: ESP32BLEProtocol.statusUUIDString)
        guard let characteristics = service.characteristics else {
            return
        }
        Task { @MainActor in
            for characteristic in characteristics {
                if characteristic.uuid == commandUUID {
                    self.commandCharacteristic = characteristic
                } else if characteristic.uuid == statusUUID {
                    self.statusCharacteristic = characteristic
                    peripheral.setNotifyValue(true, for: characteristic)
                    peripheral.readValue(for: characteristic)
                }
            }
            if self.commandCharacteristic != nil, self.statusCharacteristic != nil {
                self.statusMessage = "Ready. Send a command."
            }
        }
    }

    nonisolated func peripheral(
        _ peripheral: CBPeripheral,
        didUpdateValueFor characteristic: CBCharacteristic,
        error: Error?
    ) {
        if let error {
            Task { @MainActor in
                self.statusMessage = "Status update failed: \(error.localizedDescription)"
            }
            return
        }
        guard characteristic.uuid == CBUUID(string: ESP32BLEProtocol.statusUUIDString) else {
            return
        }
        guard let data = characteristic.value, let line = String(data: data, encoding: .utf8) else {
            return
        }
        let parsed = ESP32BLEProtocol.parseStatus(line)
        Task { @MainActor in
            self.adoptStatus(parsed)
            self.recordStatusLine(line)
        }
    }

    nonisolated func peripheral(
        _ peripheral: CBPeripheral,
        didWriteValueFor characteristic: CBCharacteristic,
        error: Error?
    ) {
        if let error {
            Task { @MainActor in
                self.statusMessage = "Write failed: \(error.localizedDescription)"
            }
        }
    }

    nonisolated func peripheral(
        _ peripheral: CBPeripheral,
        didUpdateNotificationStateFor characteristic: CBCharacteristic,
        error: Error?
    ) {
        if let error {
            Task { @MainActor in
                self.statusMessage = "Notify subscribe failed: \(error.localizedDescription)"
            }
        }
    }
}
