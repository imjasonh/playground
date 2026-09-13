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
    @Published var statusMessage = "Flash esp32-ble, then scan."

    private var central: CBCentralManager?
    private var peripherals: [UUID: CBPeripheral] = [:]
    private var connectedPeripheral: CBPeripheral?
    private var commandCharacteristic: CBCharacteristic?
    private var statusCharacteristic: CBCharacteristic?

    private let serviceUUID = CBUUID(string: ESP32BLEProtocol.serviceUUIDString)
    private let commandUUID = CBUUID(string: ESP32BLEProtocol.commandUUIDString)
    private let statusUUID = CBUUID(string: ESP32BLEProtocol.statusUUIDString)

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
        if central == nil {
            central = CBCentralManager(delegate: self, queue: nil)
        }
        applyBluetoothState(central?.state ?? .unknown)
    }

    func stop() {
        disconnect()
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
            disconnect()
        }
        devices = []
        peripherals.removeAll()
        phase = .scanning
        statusMessage = "Scanning for \(ESP32BLEProtocol.deviceName)."
        central.scanForPeripherals(
            withServices: [serviceUUID],
            options: [CBCentralManagerScanOptionAllowDuplicatesKey: true]
        )
    }

    func connect(to advertisement: ESP32BLEAdvertisement) {
        guard let central, let peripheral = peripherals[advertisement.id] else {
            statusMessage = "That device is no longer in range. Scan again."
            return
        }
        central.stopScan()
        connectedPeripheral = peripheral
        connectedName = advertisement.name
        peripheral.delegate = self
        phase = .connecting
        statusMessage = "Connecting to \(advertisement.name)."
        central.connect(peripheral, options: nil)
    }

    func disconnect() {
        if let central, let peripheral = connectedPeripheral {
            central.cancelPeripheralConnection(peripheral)
        }
        clearConnection()
        if phase == .connected || phase == .connecting {
            phase = .idle
            statusMessage = "Disconnected."
        }
    }

    func send(_ command: ESP32BLECommand) {
        sendRaw(ESP32BLEProtocol.encode(command))
    }

    func sendDraft() {
        let raw = commandDraft.trimmingCharacters(in: .whitespacesAndNewlines)
        if raw.isEmpty {
            statusMessage = "Type a command first."
            return
        }
        sendRaw(raw)
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
        if state != .poweredOn, phase == .scanning {
            central?.stopScan()
            phase = .idle
        }
        if phase == .idle || phase == .scanning {
            statusMessage = availabilitySummary
        }
        if state == .poweredOn, phase == .idle {
            startScan()
        }
    }

    private func clearConnection() {
        connectedPeripheral = nil
        commandCharacteristic = nil
        statusCharacteristic = nil
        connectedName = ""
        status = nil
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
                self.devices.sort { $0.rssi > $1.rssi }
            }
        }
    }

    nonisolated func centralManager(_ central: CBCentralManager, didConnect peripheral: CBPeripheral) {
        let service = CBUUID(string: ESP32BLEProtocol.serviceUUIDString)
        Task { @MainActor in
            self.phase = .connected
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
            self.clearConnection()
            self.phase = .idle
            self.statusMessage = "Connect failed: \(detail)"
        }
    }

    nonisolated func centralManager(
        _ central: CBCentralManager,
        didDisconnectPeripheral peripheral: CBPeripheral,
        error: Error?
    ) {
        let detail = error?.localizedDescription
        Task { @MainActor in
            self.clearConnection()
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
            self.status = parsed
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
