import CoreBluetooth

/// Core Bluetooth types are not Sendable. `ESP32BLEController` hops them from
/// delegate callbacks onto the main actor. These conformances make that hop
/// explicit.
extension CBPeripheral: @unchecked @retroactive Sendable {}
extension CBCharacteristic: @unchecked @retroactive Sendable {}
extension CBService: @unchecked @retroactive Sendable {}
extension CBCentralManager: @unchecked @retroactive Sendable {}
