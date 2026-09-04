import CoreNFC

/// Core NFC session types are not Sendable. `NFCTagsController` hops them
/// from session callbacks onto the main actor. These conformances make that
/// hop explicit.
extension NFCTagReaderSession: @unchecked @retroactive Sendable {}
extension NFCNDEFMessage: @unchecked @retroactive Sendable {}
extension NFCTag: @unchecked @retroactive Sendable {}

/// Protocol existentials cannot inherit `Sendable`. Box them before a hop.
struct NFCUncheckedSend<Value>: @unchecked Sendable {
    let value: Value
}
