import CoreNFC

/// Core NFC session types are not Sendable. `NFCTagsController` hops them
/// from session callbacks onto the main actor. These conformances make that
/// hop explicit.
extension NFCTagReaderSession: @unchecked @retroactive Sendable {}
extension NFCNDEFMessage: @unchecked @retroactive Sendable {}
extension NFCTag: @unchecked @retroactive Sendable {}
extension NFCNDEFTag: @unchecked @retroactive Sendable {}
extension NFCMiFareTag: @unchecked @retroactive Sendable {}
