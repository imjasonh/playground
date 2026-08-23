import Combine
@preconcurrency import CoreNFC
import Foundation

/// Drives Core NFC tag sessions for the NFC Tags experiment.
///
/// Uses `NFCTagReaderSession` (not NDEF-only discovery) so blank NTAG / Type 2
/// tags still surface UID and family the way apps like NFC Tools do.
///
/// NTAG / Ultralight writes go through raw Type 2 page WRITE commands and are
/// verified with raw READ of user memory. Core NFC `writeNDEF`/`readNDEF` can
/// report success from a soft/cached view that does not match EEPROM. Non-Type-2
/// tags still use `writeNDEF`, then a brand-new session must re-read matching
/// bytes before success is claimed.
///
/// Broad polling (ISO 14443 / 15693 / FeliCa) needs matching Info.plist keys:
/// `iso7816.select-identifiers` and `felica.systemcodes`. Without those, Core
/// NFC invalidates the session with "Missing required entitlement".
@MainActor
final class NFCTagsController: NSObject, ObservableObject {
    enum Mode: String {
        case read
        case write
    }

    @Published var mode: Mode = .read
    @Published var draft = NFCNDEFWriteDraft()
    @Published var statusMessage = "Hold an NFC tag near the top of the iPhone."
    @Published var lastReadSummary = ""
    @Published var isSessionActive = false

    private var tagSession: NFCTagReaderSession?
    private var pendingWriteMessage: NFCNDEFMessage?
    /// Survives session invalidate so a follow-up confirm session can re-read.
    private var pendingDurabilityExpected: [NFCNDEFRecordSnapshot]?
    /// True while intentionally ending the write session to open a confirm session.
    private var expectingDurabilityRestart = false

    var isNFCAvailable: Bool {
        NFCTagReaderSession.readingAvailable
    }

    func startRead() {
        guard isNFCAvailable else {
            statusMessage = "NFC is not available on this device or the Simulator."
            return
        }
        pendingWriteMessage = nil
        pendingDurabilityExpected = nil
        beginSession(alertMessage: "Hold an NFC tag near the top of the iPhone to read it.")
    }

    func startWrite() {
        guard isNFCAvailable else {
            statusMessage = "NFC is not available on this device or the Simulator."
            return
        }
        if let error = NFCNDEFCodec.validationError(for: draft) {
            statusMessage = error
            return
        }
        guard let message = makeWriteMessage() else {
            statusMessage = "Could not build an NDEF message from that input."
            return
        }
        pendingWriteMessage = message
        pendingDurabilityExpected = nil
        beginSession(alertMessage: "Hold a writable NFC tag near the top of the iPhone.")
    }

    func cancelSession() {
        expectingDurabilityRestart = false
        tagSession?.invalidate()
        tagSession = nil
        pendingWriteMessage = nil
        pendingDurabilityExpected = nil
        isSessionActive = false
    }

    // MARK: - Session

    private func beginSession(alertMessage: String) {
        // Keep durability expectations across an intentional confirm restart.
        let durability = pendingDurabilityExpected
        tagSession?.invalidate()
        tagSession = nil
        pendingWriteMessage = nil
        isSessionActive = false
        pendingDurabilityExpected = durability

        guard let session = NFCTagReaderSession(
            pollingOption: [.iso14443, .iso15693, .iso18092],
            delegate: self,
            queue: nil
        ) else {
            statusMessage = "NFC is not available on this device or the Simulator."
            return
        }
        session.alertMessage = alertMessage
        tagSession = session
        isSessionActive = true
        statusMessage = alertMessage
        session.begin()
    }

    private func makeWriteMessage() -> NFCNDEFMessage? {
        let trimmed = draft.text.trimmingCharacters(in: .whitespacesAndNewlines)
        switch draft.kind {
        case .text:
            let payload = NFCNDEFCodec.encodeTextPayload(text: trimmed, languageCode: "en")
            let record = NFCNDEFPayload(
                format: .nfcWellKnown,
                type: Data("T".utf8),
                identifier: Data(),
                payload: payload
            )
            return NFCNDEFMessage(records: [record])
        case .url:
            guard let payload = NFCNDEFCodec.encodeURIPayload(urlString: trimmed) else {
                return nil
            }
            let record = NFCNDEFPayload(
                format: .nfcWellKnown,
                type: Data("U".utf8),
                identifier: Data(),
                payload: payload
            )
            return NFCNDEFMessage(records: [record])
        }
    }

    private func decode(_ message: NFCNDEFMessage) -> [NFCNDEFDecodedRecord] {
        message.records.map { record in
            NFCNDEFCodec.decodeRecord(
                typeNameFormatRawValue: record.typeNameFormat.rawValue,
                type: record.type,
                payload: record.payload
            )
        }
    }

    private func snapshots(from message: NFCNDEFMessage) -> [NFCNDEFRecordSnapshot] {
        message.records.map { record in
            NFCNDEFRecordSnapshot(
                typeNameFormatRawValue: record.typeNameFormat.rawValue,
                type: record.type,
                payload: record.payload
            )
        }
    }

    private func finish(session: NFCTagReaderSession, alert: String) {
        pendingDurabilityExpected = nil
        statusMessage = alert
        session.alertMessage = alert
        session.invalidate()
    }

    private func clearSessionIfCurrent(_ session: NFCTagReaderSession) {
        guard session === tagSession else { return }
        tagSession = nil
        pendingWriteMessage = nil
        isSessionActive = false
        // Leave pendingDurabilityExpected so a confirm session can start.
    }

    /// Ends the write session and opens a new one that must re-read matching bytes.
    private func startDurabilityConfirm(
        expected: [NFCNDEFRecordSnapshot],
        ending session: NFCTagReaderSession
    ) {
        pendingWriteMessage = nil
        pendingDurabilityExpected = expected
        expectingDurabilityRestart = true
        statusMessage = "Remove the tag, then hold it again to confirm the write."
        session.alertMessage = statusMessage
        session.invalidate()
        Task { @MainActor in
            // Let the system tear down RF before polling again.
            try? await Task.sleep(nanoseconds: 400_000_000)
            self.expectingDurabilityRestart = false
            guard self.pendingDurabilityExpected != nil else { return }
            self.beginSession(
                alertMessage: "Hold the tag again to confirm the write stuck."
            )
        }
    }
}

// MARK: - Detected tag identity

private struct DetectedNFCTag {
    var ndefTag: NFCNDEFTag
    var miFare: NFCMiFareTag?
    var uid: String?
    var family: String
}

extension NFCTagsController {
    private func describe(_ tag: NFCTag) -> DetectedNFCTag? {
        switch tag {
        case .miFare(let miFare):
            return DetectedNFCTag(
                ndefTag: miFare,
                miFare: miFare,
                uid: NFCTagScanFormatter.uidHex(miFare.identifier),
                family: "ISO 14443 (NTAG / MiFare)"
            )
        case .feliCa(let feliCa):
            return DetectedNFCTag(
                ndefTag: feliCa,
                miFare: nil,
                uid: NFCTagScanFormatter.uidHex(feliCa.currentIDm),
                family: "FeliCa"
            )
        case .iso15693(let iso15693):
            return DetectedNFCTag(
                ndefTag: iso15693,
                miFare: nil,
                uid: NFCTagScanFormatter.uidHex(iso15693.identifier),
                family: "ISO 15693"
            )
        case .iso7816(let iso7816):
            let uid = iso7816.identifier.isEmpty
                ? nil
                : NFCTagScanFormatter.uidHex(iso7816.identifier)
            return DetectedNFCTag(
                ndefTag: iso7816,
                miFare: nil,
                uid: uid,
                family: "ISO 7816"
            )
        @unknown default:
            return nil
        }
    }

    private func supportsType2Raw(_ miFare: NFCMiFareTag) -> Bool {
        switch miFare.mifareFamily {
        case .ultralight, .unknown:
            // NTAG21x often reports as `.unknown` on iOS.
            return true
        case .desfire, .plus:
            return false
        @unknown default:
            return false
        }
    }
}

// MARK: - NFCTagReaderSessionDelegate

extension NFCTagsController: NFCTagReaderSessionDelegate {
    nonisolated func tagReaderSessionDidBecomeActive(_ session: NFCTagReaderSession) {}

    nonisolated func tagReaderSession(
        _ session: NFCTagReaderSession,
        didInvalidateWithError error: Error
    ) {
        Task { @MainActor in
            self.clearSessionIfCurrent(session)

            let nsError = error as NSError
            guard nsError.domain == NFCReaderError.errorDomain else {
                if self.pendingDurabilityExpected == nil {
                    self.statusMessage = error.localizedDescription
                }
                return
            }
            let benign: Set<Int> = [
                NFCReaderError.readerSessionInvalidationErrorUserCanceled.rawValue,
                NFCReaderError.readerSessionInvalidationErrorFirstNDEFTagRead.rawValue,
            ]
            if benign.contains(nsError.code) {
                // User cancel on the system sheet drops a pending confirm, unless
                // we invalidated on purpose to open the confirm session.
                if nsError.code
                    == NFCReaderError.readerSessionInvalidationErrorUserCanceled.rawValue,
                    !self.expectingDurabilityRestart
                {
                    self.pendingDurabilityExpected = nil
                }
                return
            }
            if self.statusMessage.hasPrefix("Wrote")
                || self.statusMessage.hasPrefix("Write ")
                || self.statusMessage.hasPrefix("Read ")
                || self.statusMessage.hasPrefix("Blank ")
                || self.statusMessage.hasPrefix("Remove the tag")
                || self.statusMessage.hasPrefix("Hold the tag again")
            {
                return
            }
            if self.pendingDurabilityExpected == nil {
                self.statusMessage = error.localizedDescription
            }
        }
    }

    nonisolated func tagReaderSession(
        _ session: NFCTagReaderSession,
        didDetect tags: [NFCTag]
    ) {
        Task { @MainActor in
            guard session === self.tagSession else { return }
            self.handleDetectedTags(tags, session: session)
        }
    }

    private func handleDetectedTags(_ tags: [NFCTag], session: NFCTagReaderSession) {
        guard let tag = tags.first else { return }
        if tags.count > 1 {
            session.alertMessage = "More than one tag detected. Remove extras and try again."
            session.restartPolling()
            return
        }

        session.connect(to: tag) { [weak self] error in
            Task { @MainActor in
                guard let self, session === self.tagSession else { return }
                if let error {
                    self.finish(
                        session: session,
                        alert: "Could not connect to the tag: \(error.localizedDescription)"
                    )
                    return
                }
                guard let detected = self.describe(tag) else {
                    self.finish(session: session, alert: "Unsupported tag type.")
                    return
                }
                if let writeMessage = self.pendingWriteMessage {
                    self.write(writeMessage, to: detected, session: session)
                } else if self.pendingDurabilityExpected != nil {
                    self.confirmDurability(on: detected, session: session)
                } else {
                    self.read(from: detected, session: session)
                }
            }
        }
    }

    private func read(from detected: DetectedNFCTag, session: NFCTagReaderSession) {
        detected.ndefTag.queryNDEFStatus { [weak self] status, capacity, error in
            Task { @MainActor in
                guard let self, session === self.tagSession else { return }
                if let error {
                    self.finish(
                        session: session,
                        alert: "Failed to query NDEF: \(error.localizedDescription)"
                    )
                    return
                }
                switch status {
                case .notSupported:
                    self.lastReadSummary = NFCTagScanFormatter.nonNDEFSummary(
                        uid: detected.uid,
                        family: detected.family
                    )
                    self.finish(session: session, alert: "Tag has no NDEF message.")
                case .readOnly, .readWrite:
                    detected.ndefTag.readNDEF { message, readError in
                        Task { @MainActor in
                            guard session === self.tagSession else { return }
                            self.handleReadNDEF(
                                message: message,
                                readError: readError,
                                writable: status == .readWrite,
                                capacity: capacity,
                                detected: detected,
                                session: session
                            )
                        }
                    }
                @unknown default:
                    self.finish(session: session, alert: "Unknown NDEF status.")
                }
            }
        }
    }

    private func handleReadNDEF(
        message: NFCNDEFMessage?,
        readError: Error?,
        writable: Bool,
        capacity: Int,
        detected: DetectedNFCTag,
        session: NFCTagReaderSession
    ) {
        if let readError {
            let nsError = readError as NSError
            let emptyNDEF = nsError.domain == NFCReaderError.errorDomain
                && NFCTagScanFormatter.isEmptyNDEFErrorCode(nsError.code)
            if emptyNDEF {
                presentBlankTag(
                    writable: writable,
                    capacity: capacity,
                    detected: detected,
                    session: session
                )
                return
            }
            finish(
                session: session,
                alert: "Failed to read NDEF: \(readError.localizedDescription)"
            )
            return
        }

        guard let message else {
            presentBlankTag(
                writable: writable,
                capacity: capacity,
                detected: detected,
                session: session
            )
            return
        }

        let records = decode(message)
        if records.isEmpty {
            presentBlankTag(
                writable: writable,
                capacity: capacity,
                detected: detected,
                session: session
            )
            return
        }

        let body = NFCNDEFCodec.summary(for: records)
        lastReadSummary = NFCTagScanFormatter.recordsSummary(
            body,
            uid: detected.uid,
            family: detected.family
        )
        let alert = "Read \(records.count) record\(records.count == 1 ? "" : "s")."
        finish(session: session, alert: alert)
    }

    private func presentBlankTag(
        writable: Bool,
        capacity: Int,
        detected: DetectedNFCTag,
        session: NFCTagReaderSession
    ) {
        lastReadSummary = NFCTagScanFormatter.blankTagSummary(
            writable: writable,
            capacity: capacity,
            uid: detected.uid,
            family: detected.family
        )
        finish(session: session, alert: "Blank NDEF tag.")
    }

    private func write(
        _ message: NFCNDEFMessage,
        to detected: DetectedNFCTag,
        session: NFCTagReaderSession
    ) {
        if let miFare = detected.miFare, supportsType2Raw(miFare) {
            writeType2Raw(to: detected, miFare: miFare, session: session)
            return
        }

        detected.ndefTag.queryNDEFStatus { [weak self] status, capacity, error in
            Task { @MainActor in
                guard let self, session === self.tagSession else { return }
                if let error {
                    self.finish(
                        session: session,
                        alert: "Failed to query NDEF: \(error.localizedDescription)"
                    )
                    return
                }
                switch status {
                case .notSupported:
                    self.finish(
                        session: session,
                        alert: "Tag is not NDEF-writable. Try a blank phone-writable NTAG."
                    )
                case .readOnly:
                    self.finish(session: session, alert: "Tag is read-only.")
                case .readWrite:
                    let length = message.length
                    if length > capacity {
                        self.finish(
                            session: session,
                            alert: "Message is \(length) bytes; tag capacity is \(capacity)."
                        )
                        return
                    }
                    detected.ndefTag.writeNDEF(message) { writeError in
                        Task { @MainActor in
                            guard session === self.tagSession else { return }
                            if let writeError {
                                self.finish(
                                    session: session,
                                    alert: "Failed to write NDEF: "
                                        + writeError.localizedDescription
                                )
                                return
                            }
                            let expected = self.snapshots(from: message)
                            self.verifyNDEFThenConfirm(
                                expected: expected,
                                on: detected,
                                session: session,
                                allowRetryWrite: message
                            )
                        }
                    }
                @unknown default:
                    self.finish(session: session, alert: "Unknown NDEF status.")
                }
            }
        }
    }

    // MARK: - Type 2 raw write / verify

    private func writeType2Raw(
        to detected: DetectedNFCTag,
        miFare: NFCMiFareTag,
        session: NFCTagReaderSession
    ) {
        guard let ndef = Type2NDEF.ndefMessage(for: draft),
              let expected = Type2NDEF.snapshots(for: draft)
        else {
            finish(session: session, alert: "Could not build an NDEF message from that input.")
            return
        }
        let tlv = Type2NDEF.wrapTLV(ndef)

        detected.ndefTag.queryNDEFStatus { [weak self] status, capacity, _ in
            Task { @MainActor in
                guard let self, session === self.tagSession else { return }
                if status == .readOnly {
                    self.finish(session: session, alert: "Tag is read-only.")
                    return
                }
                let ndefCapacity = capacity > 0 ? capacity : max(tlv.count, 48)
                if tlv.count > ndefCapacity + 16 {
                    self.finish(
                        session: session,
                        alert: "Message is \(tlv.count) bytes; tag capacity is \(ndefCapacity)."
                    )
                    return
                }
                self.ensureCapabilityContainer(
                    miFare: miFare,
                    ndefCapacity: ndefCapacity,
                    session: session
                ) { ccError in
                    if let ccError {
                        self.finish(
                            session: session,
                            alert: "Failed to format tag: \(ccError.localizedDescription)"
                        )
                        return
                    }
                    self.writeType2Pages(
                        miFare: miFare,
                        tlv: tlv,
                        session: session
                    ) { writeError in
                        if let writeError {
                            self.finish(
                                session: session,
                                alert: "Failed to write tag pages: "
                                    + writeError.localizedDescription
                            )
                            return
                        }
                        self.verifyType2Raw(
                            miFare: miFare,
                            expectedNDEF: ndef,
                            session: session
                        ) { verifyError in
                            if let verifyError {
                                self.finish(
                                    session: session,
                                    alert: "Write did not stick on chip: "
                                        + verifyError.localizedDescription
                                )
                                return
                            }
                            self.startDurabilityConfirm(expected: expected, ending: session)
                        }
                    }
                }
            }
        }
    }

    private func ensureCapabilityContainer(
        miFare: NFCMiFareTag,
        ndefCapacity: Int,
        session: NFCTagReaderSession,
        completion: @escaping (Error?) -> Void
    ) {
        miFare.sendMiFareCommand(
            commandPacket: Type2NDEF.readCommandPacket(page: Type2NDEF.capabilityContainerPage)
        ) { response, error in
            Task { @MainActor in
                guard session === self.tagSession else { return }
                if let error {
                    completion(error)
                    return
                }
                guard response.count >= 4 else {
                    completion(
                        NSError(
                            domain: "NFCTags",
                            code: 1,
                            userInfo: [
                                NSLocalizedDescriptionKey: "Short READ response for page 3.",
                            ]
                        )
                    )
                    return
                }
                let page3 = Data(response.prefix(4))
                if Type2NDEF.hasNDEFCapabilityContainer(page3) {
                    completion(nil)
                    return
                }
                let cc = Type2NDEF.capabilityContainer(ndefCapacity: ndefCapacity)
                let bytes = [UInt8](cc)
                miFare.sendMiFareCommand(
                    commandPacket: Type2NDEF.writeCommandPacket(
                        page: Type2NDEF.capabilityContainerPage,
                        bytes: bytes
                    )
                ) { _, writeError in
                    Task { @MainActor in
                        guard session === self.tagSession else { return }
                        completion(writeError)
                    }
                }
            }
        }
    }

    private func writeType2Pages(
        miFare: NFCMiFareTag,
        tlv: Data,
        session: NFCTagReaderSession,
        completion: @escaping (Error?) -> Void
    ) {
        let pages = Type2NDEF.pages(from: tlv)
        var index = 0

        func writeNext() {
            guard session === self.tagSession else { return }
            if index >= pages.count {
                completion(nil)
                return
            }
            let pageNumber = Type2NDEF.ndefTLVStartPage + UInt8(index)
            let packet = Type2NDEF.writeCommandPacket(page: pageNumber, bytes: pages[index])
            miFare.sendMiFareCommand(commandPacket: packet) { _, error in
                Task { @MainActor in
                    guard session === self.tagSession else { return }
                    if let error {
                        completion(error)
                        return
                    }
                    index += 1
                    writeNext()
                }
            }
        }

        writeNext()
    }

    private func verifyType2Raw(
        miFare: NFCMiFareTag,
        expectedNDEF: Data,
        session: NFCTagReaderSession,
        completion: @escaping (Error?) -> Void
    ) {
        // Read enough user memory to cover TLV header + message + terminator.
        let needed = expectedNDEF.count + 8
        readType2UserMemory(miFare: miFare, byteCount: needed, session: session) { result in
            switch result {
            case .failure(let error):
                completion(error)
            case .success(let memory):
                guard let actual = Type2NDEF.extractNDEFMessage(fromUserMemory: memory) else {
                    completion(
                        NSError(
                            domain: "NFCTags",
                            code: 2,
                            userInfo: [
                                NSLocalizedDescriptionKey: "No NDEF TLV found after write.",
                            ]
                        )
                    )
                    return
                }
                guard actual == expectedNDEF else {
                    completion(
                        NSError(
                            domain: "NFCTags",
                            code: 3,
                            userInfo: [
                                NSLocalizedDescriptionKey: "EEPROM bytes do not match what was written.",
                            ]
                        )
                    )
                    return
                }
                completion(nil)
            }
        }
    }

    private func readType2UserMemory(
        miFare: NFCMiFareTag,
        byteCount: Int,
        session: NFCTagReaderSession,
        completion: @escaping (Result<Data, Error>) -> Void
    ) {
        var collected = Data()
        var page = Type2NDEF.ndefTLVStartPage

        func readNext() {
            guard session === self.tagSession else { return }
            if collected.count >= byteCount || page > 220 {
                completion(.success(collected))
                return
            }
            miFare.sendMiFareCommand(
                commandPacket: Type2NDEF.readCommandPacket(page: page)
            ) { response, error in
                Task { @MainActor in
                    guard session === self.tagSession else { return }
                    if let error {
                        completion(.failure(error))
                        return
                    }
                    guard let response, response.count >= 16 else {
                        completion(
                            .failure(
                                NSError(
                                    domain: "NFCTags",
                                    code: 4,
                                    userInfo: [
                                        NSLocalizedDescriptionKey: "Short READ response.",
                                    ]
                                )
                            )
                        )
                        return
                    }
                    collected.append(response.prefix(16))
                    page += 4
                    readNext()
                }
            }
        }

        readNext()
    }

    /// High-level NDEF verify (non-Type-2 path), then new-session confirm.
    private func verifyNDEFThenConfirm(
        expected: [NFCNDEFRecordSnapshot],
        on detected: DetectedNFCTag,
        session: NFCTagReaderSession,
        allowRetryWrite: NFCNDEFMessage?
    ) {
        detected.ndefTag.readNDEF { message, readError in
            Task { @MainActor in
                guard session === self.tagSession else { return }
                let stillBlank: Bool = {
                    if let readError {
                        let nsError = readError as NSError
                        return nsError.domain == NFCReaderError.errorDomain
                            && NFCTagScanFormatter.isEmptyNDEFErrorCode(nsError.code)
                    }
                    return message == nil || message?.records.isEmpty == true
                }()

                if stillBlank, let retry = allowRetryWrite {
                    detected.ndefTag.writeNDEF(retry) { retryError in
                        Task { @MainActor in
                            guard session === self.tagSession else { return }
                            if let retryError {
                                self.finish(
                                    session: session,
                                    alert: "Write did not stick; retry failed: "
                                        + retryError.localizedDescription
                                )
                                return
                            }
                            self.verifyNDEFThenConfirm(
                                expected: expected,
                                on: detected,
                                session: session,
                                allowRetryWrite: nil
                            )
                        }
                    }
                    return
                }

                if let readError {
                    self.finish(
                        session: session,
                        alert: "Wrote, but could not verify: \(readError.localizedDescription)"
                    )
                    return
                }
                guard let message else {
                    self.finish(
                        session: session,
                        alert: "Write reported success, but the tag is still blank."
                    )
                    return
                }
                let actual = self.snapshots(from: message)
                guard NFCNDEFCodec.ndefRecordsMatch(expected, actual) else {
                    self.finish(
                        session: session,
                        alert: "Write did not update the tag "
                            + "(read-back does not match what was written)."
                    )
                    return
                }
                self.startDurabilityConfirm(expected: expected, ending: session)
            }
        }
    }

    /// Second session after remove/re-present; must match expected snapshots.
    private func confirmDurability(
        on detected: DetectedNFCTag,
        session: NFCTagReaderSession
    ) {
        guard let expected = pendingDurabilityExpected else {
            read(from: detected, session: session)
            return
        }

        // Prefer raw EEPROM check on Type 2 when available.
        if let miFare = detected.miFare,
           supportsType2Raw(miFare),
           let ndef = Type2NDEF.ndefMessage(for: draft),
           NFCNDEFCodec.ndefRecordsMatch(expected, Type2NDEF.snapshots(for: draft) ?? [])
        {
            verifyType2Raw(miFare: miFare, expectedNDEF: ndef, session: session) { error in
                if let error {
                    self.finish(
                        session: session,
                        alert: "Write looked OK, but chip confirm failed: "
                            + error.localizedDescription
                    )
                    return
                }
                self.completeDurabilitySuccess(
                    expected: expected,
                    detected: detected,
                    session: session,
                    byteCount: ndef.count
                )
            }
            return
        }

        detected.ndefTag.readNDEF { message, readError in
            Task { @MainActor in
                guard session === self.tagSession else { return }
                if let readError {
                    self.finish(
                        session: session,
                        alert: "Write looked OK, but confirm failed: "
                            + readError.localizedDescription
                    )
                    return
                }
                guard let message else {
                    self.finish(
                        session: session,
                        alert: "Write looked OK, but a second read found no NDEF message."
                    )
                    return
                }
                let actual = self.snapshots(from: message)
                guard NFCNDEFCodec.ndefRecordsMatch(expected, actual) else {
                    self.finish(
                        session: session,
                        alert: "Write looked OK, but a second read did not match. Try again."
                    )
                    return
                }
                self.completeDurabilitySuccess(
                    expected: expected,
                    detected: detected,
                    session: session,
                    byteCount: message.length
                )
            }
        }
    }

    private func completeDurabilitySuccess(
        expected: [NFCNDEFRecordSnapshot],
        detected: DetectedNFCTag,
        session: NFCTagReaderSession,
        byteCount: Int
    ) {
        pendingDurabilityExpected = nil
        let records = expected.map { snap in
            NFCNDEFCodec.decodeRecord(
                typeNameFormatRawValue: snap.typeNameFormatRawValue,
                type: snap.type,
                payload: snap.payload
            )
        }
        let body = NFCNDEFCodec.summary(for: records)
        lastReadSummary = NFCTagScanFormatter.recordsSummary(
            body,
            uid: detected.uid,
            family: detected.family
        )
        finish(
            session: session,
            alert: "Wrote and verified NDEF message (\(byteCount) bytes)."
        )
    }
}
