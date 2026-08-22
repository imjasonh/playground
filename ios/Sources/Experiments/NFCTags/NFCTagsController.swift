import Combine
@preconcurrency import CoreNFC
import Foundation

/// Drives Core NFC tag sessions for the NFC Tags experiment.
///
/// Uses `NFCTagReaderSession` (not NDEF-only discovery) so blank NTAG / Type 2
/// tags still surface UID and family the way apps like NFC Tools do. NDEF
/// read/write runs through the tag's `NFCNDEFTag` interface after connect.
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

    var isNFCAvailable: Bool {
        NFCTagReaderSession.readingAvailable
    }

    func startRead() {
        guard isNFCAvailable else {
            statusMessage = "NFC is not available on this device or the Simulator."
            return
        }
        pendingWriteMessage = nil
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
        beginSession(alertMessage: "Hold a writable NFC tag near the top of the iPhone.")
    }

    func cancelSession() {
        tagSession?.invalidate()
        tagSession = nil
        pendingWriteMessage = nil
        isSessionActive = false
    }

    // MARK: - Session

    private func beginSession(alertMessage: String) {
        // Drop any prior session before starting. Its invalidate callback must
        // not clear the new session; see didInvalidateWithError.
        cancelSession()
        // NFCTagReaderSession's initializer is failable (nil when NFC is
        // unavailable, e.g. Simulator).
        // Poll ISO 14443 (NTAG / MiFare) and ISO 15693 only. Do not include
        // .iso18092 (FeliCa): that option requires
        // com.apple.developer.nfc.readersession.felica.systemcodes in
        // Info.plist, and without it the session invalidates immediately with
        // "Missing required entitlement".
        guard let session = NFCTagReaderSession(
            pollingOption: [.iso14443, .iso15693],
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

    private func finish(session: NFCTagReaderSession, alert: String) {
        statusMessage = alert
        session.alertMessage = alert
        session.invalidate()
    }

    private func clearSessionIfCurrent(_ session: NFCTagReaderSession) {
        guard session === tagSession else { return }
        tagSession = nil
        pendingWriteMessage = nil
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
                            self.pendingWriteMessage = nil
                            self.finish(
                                session: session,
                                alert: "Wrote NDEF message (\(length) bytes)."
                            )
                        }
                    }
                @unknown default:
                    self.finish(session: session, alert: "Unknown NDEF status.")
                }
            }
        }
    }
}
