import Combine
@preconcurrency import CoreNFC
import Foundation

/// Drives Core NFC tag sessions for the NFC Tags experiment.
///
/// Uses `NFCTagReaderSession` (not NDEF-only discovery) so blank NTAG / Type 2
/// tags still surface UID and family the way apps like NFC Tools do. NDEF
/// read/write runs through the tag's `NFCNDEFTag` interface after connect.
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
    /// After a same-session write match, re-poll and require a second read that
    /// matches these snapshots so a soft/cached success cannot pass as durable.
    private var pendingDurabilityExpected: [NFCNDEFRecordSnapshot]?

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
        tagSession?.invalidate()
        tagSession = nil
        pendingWriteMessage = nil
        pendingDurabilityExpected = nil
        isSessionActive = false
    }

    // MARK: - Session

    private func beginSession(alertMessage: String) {
        // Drop any prior session before starting. Its invalidate callback must
        // not clear the new session; see didInvalidateWithError.
        cancelSession()
        // NFCTagReaderSession's initializer is failable (nil when NFC is
        // unavailable, e.g. Simulator). Poll all tag families NFC Tools-style;
        // Info.plist must list FeliCa system codes and ISO 7816 AIDs.
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
            guard let payload = NFCNDEFPayload.wellKnownTypeTextPayload(
                string: trimmed,
                locale: Locale(identifier: "en")
            ) else {
                return nil
            }
            return NFCNDEFMessage(records: [payload])
        case .url:
            guard let url = URL(string: trimmed),
                  let payload = NFCNDEFPayload.wellKnownTypeURIPayload(url: url)
            else {
                return nil
            }
            return NFCNDEFMessage(records: [payload])
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
        pendingDurabilityExpected = nil
        isSessionActive = false
    }
}

// MARK: - Detected tag identity

private struct DetectedNFCTag {
    var ndefTag: NFCNDEFTag
    var uid: String?
    var family: String
}

extension NFCTagsController {
    private func describe(_ tag: NFCTag) -> DetectedNFCTag? {
        switch tag {
        case .miFare(let miFare):
            return DetectedNFCTag(
                ndefTag: miFare,
                uid: NFCTagScanFormatter.uidHex(miFare.identifier),
                family: "ISO 14443 (NTAG / MiFare)"
            )
        case .feliCa(let feliCa):
            return DetectedNFCTag(
                ndefTag: feliCa,
                uid: NFCTagScanFormatter.uidHex(feliCa.currentIDm),
                family: "FeliCa"
            )
        case .iso15693(let iso15693):
            return DetectedNFCTag(
                ndefTag: iso15693,
                uid: NFCTagScanFormatter.uidHex(iso15693.identifier),
                family: "ISO 15693"
            )
        case .iso7816(let iso7816):
            let uid = iso7816.identifier.isEmpty
                ? nil
                : NFCTagScanFormatter.uidHex(iso7816.identifier)
            return DetectedNFCTag(
                ndefTag: iso7816,
                uid: uid,
                family: "ISO 7816"
            )
        @unknown default:
            return nil
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
            // A superseded session must not wipe a newer beginSession().
            self.clearSessionIfCurrent(session)

            let nsError = error as NSError
            guard nsError.domain == NFCReaderError.errorDomain else {
                self.statusMessage = error.localizedDescription
                return
            }
            // Expected endings after a successful finish() or user Cancel.
            let benign: Set<Int> = [
                NFCReaderError.readerSessionInvalidationErrorUserCanceled.rawValue,
                NFCReaderError.readerSessionInvalidationErrorFirstNDEFTagRead.rawValue,
            ]
            if benign.contains(nsError.code) {
                return
            }
            // invalidate() after a successful finish() can still deliver a
            // non-benign error; keep write/read outcome status.
            if self.statusMessage.hasPrefix("Wrote")
                || self.statusMessage.hasPrefix("Write ")
                || self.statusMessage.hasPrefix("Read ")
                || self.statusMessage.hasPrefix("Blank ")
            {
                return
            }
            self.statusMessage = error.localizedDescription
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
                                    alert: "Failed to write NDEF: \(writeError.localizedDescription)"
                                )
                                return
                            }
                            // Core NFC can report write success on blank Type 2
                            // tags without persisting. Confirm with a read-back
                            // before claiming success; retry once if still blank.
                            self.verifyWrite(
                                message,
                                on: detected,
                                session: session,
                                allowRetry: true
                            )
                        }
                    }
                @unknown default:
                    self.finish(session: session, alert: "Unknown NDEF status.")
                }
            }
        }
    }

    /// Reads the tag after writeNDEF and only then reports success.
    private func verifyWrite(
        _ written: NFCNDEFMessage,
        on detected: DetectedNFCTag,
        session: NFCTagReaderSession,
        allowRetry: Bool
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

                if stillBlank, allowRetry {
                    detected.ndefTag.writeNDEF(written) { retryError in
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
                            self.verifyWrite(
                                written,
                                on: detected,
                                session: session,
                                allowRetry: false
                            )
                        }
                    }
                    return
                }

                if let readError {
                    let nsError = readError as NSError
                    let emptyNDEF = nsError.domain == NFCReaderError.errorDomain
                        && NFCTagScanFormatter.isEmptyNDEFErrorCode(nsError.code)
                    if emptyNDEF {
                        self.finish(
                            session: session,
                            alert: "Write reported success, but the tag is still blank. "
                                + "Try again, or format the tag once with NFC Tools."
                        )
                        return
                    }
                    self.finish(
                        session: session,
                        alert: "Wrote, but could not verify: \(readError.localizedDescription)"
                    )
                    return
                }
                guard let message, !message.records.isEmpty else {
                    self.finish(
                        session: session,
                        alert: "Write reported success, but the tag is still blank. "
                            + "Try again, or format the tag once with NFC Tools."
                    )
                    return
                }

                let expected = self.snapshots(from: written)
                let actual = self.snapshots(from: message)
                guard NFCNDEFCodec.ndefRecordsMatch(expected, actual) else {
                    self.finish(
                        session: session,
                        alert: "Write did not update the tag "
                            + "(read-back does not match what was written)."
                    )
                    return
                }

                // Same-session match can still be a soft/cached view. Re-poll and
                // require a second connect/read before claiming durable success.
                self.pendingWriteMessage = nil
                self.pendingDurabilityExpected = expected
                let confirm = "Hold still to confirm the write stuck."
                session.alertMessage = confirm
                self.statusMessage = confirm
                session.restartPolling()
            }
        }
    }

    /// Second read after restartPolling; must match the written snapshots.
    private func confirmDurability(
        on detected: DetectedNFCTag,
        session: NFCTagReaderSession
    ) {
        guard let expected = pendingDurabilityExpected else {
            read(from: detected, session: session)
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

                self.pendingDurabilityExpected = nil
                let records = self.decode(message)
                let body = NFCNDEFCodec.summary(for: records)
                self.lastReadSummary = NFCTagScanFormatter.recordsSummary(
                    body,
                    uid: detected.uid,
                    family: detected.family
                )
                self.finish(
                    session: session,
                    alert: "Wrote and verified NDEF message (\(message.length) bytes)."
                )
            }
        }
    }
}
