import Combine
import CoreNFC
import Foundation

/// Drives Core NFC NDEF read and write sessions for the NFC Tags experiment.
@MainActor
final class NFCTagsController: NSObject, ObservableObject {
    enum Mode: String {
        case read
        case write
    }

    @Published var mode: Mode = .read
    @Published var draft = NFCNDEFWriteDraft()
    @Published var statusMessage = "Hold an NDEF tag near the top of the iPhone."
    @Published var lastReadSummary = ""
    @Published var isSessionActive = false

    private var readerSession: NFCNDEFReaderSession?
    private var pendingWriteMessage: NFCNDEFMessage?

    var isNFCAvailable: Bool {
        NFCNDEFReaderSession.readingAvailable
    }

    func startRead() {
        guard isNFCAvailable else {
            statusMessage = "NFC is not available on this device (or the Simulator)."
            return
        }
        pendingWriteMessage = nil
        beginSession(alertMessage: "Hold an NDEF tag near the top of the iPhone to read it.")
    }

    func startWrite() {
        guard isNFCAvailable else {
            statusMessage = "NFC is not available on this device (or the Simulator)."
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
        beginSession(alertMessage: "Hold a writable NDEF tag near the top of the iPhone.")
    }

    func cancelSession() {
        readerSession?.invalidate()
        readerSession = nil
        pendingWriteMessage = nil
        isSessionActive = false
    }

    // MARK: - Session

    private func beginSession(alertMessage: String) {
        cancelSession()
        // invalidateAfterFirstRead must be false so we can connect and write
        // (and so read can use the tag APIs after detection).
        let session = NFCNDEFReaderSession(
            delegate: self,
            queue: nil,
            invalidateAfterFirstRead: false
        )
        session.alertMessage = alertMessage
        readerSession = session
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

    private func finish(session: NFCNDEFReaderSession, alert: String) {
        statusMessage = alert
        session.alertMessage = alert
        session.invalidate()
    }
}

// MARK: - NFCNDEFReaderSessionDelegate

extension NFCTagsController: NFCNDEFReaderSessionDelegate {
    nonisolated func readerSessionDidBecomeActive(_ session: NFCNDEFReaderSession) {}

    nonisolated func readerSession(_ session: NFCNDEFReaderSession, didInvalidateWithError error: Error) {
        Task { @MainActor in
            self.isSessionActive = false
            self.readerSession = nil
            self.pendingWriteMessage = nil
            let nsError = error as NSError
            // User cancelled — keep the prior status rather than flashing an error.
            if nsError.domain == NFCReaderError.errorDomain,
               nsError.code == NFCReaderError.readerSessionInvalidationErrorUserCanceled.rawValue {
                return
            }
            self.statusMessage = error.localizedDescription
        }
    }

    nonisolated func readerSession(
        _ session: NFCNDEFReaderSession,
        didDetectNDEFs messages: [NFCNDEFMessage]
    ) {
        // Prefer didDetect tags for connect / write. This path covers older
        // read-only discovery when tags are already NDEF-formatted.
        Task { @MainActor in
            guard self.pendingWriteMessage == nil else { return }
            let records = messages.flatMap { self.decode($0) }
            self.lastReadSummary = NFCNDEFCodec.summary(for: records)
            let alert = "Read \(records.count) record\(records.count == 1 ? "" : "s")."
            self.finish(session: session, alert: alert)
        }
    }

    nonisolated func readerSession(_ session: NFCNDEFReaderSession, didDetect tags: [NFCNDEFTag]) {
        Task { @MainActor in
            self.handleDetectedTags(tags, session: session)
        }
    }

    private func handleDetectedTags(_ tags: [NFCNDEFTag], session: NFCNDEFReaderSession) {
        guard let tag = tags.first else { return }
        if tags.count > 1 {
            session.alertMessage = "More than one tag detected. Remove extras and try again."
            session.restartPolling()
            return
        }

        session.connect(to: tag) { [weak self] error in
            Task { @MainActor in
                guard let self else { return }
                if let error {
                    self.finish(
                        session: session,
                        alert: "Could not connect to the tag: \(error.localizedDescription)"
                    )
                    return
                }
                if let writeMessage = self.pendingWriteMessage {
                    self.write(writeMessage, to: tag, session: session)
                } else {
                    self.read(from: tag, session: session)
                }
            }
        }
    }

    private func read(from tag: NFCNDEFTag, session: NFCNDEFReaderSession) {
        tag.queryNDEFStatus { [weak self] status, _, error in
            Task { @MainActor in
                guard let self else { return }
                if let error {
                    self.finish(
                        session: session,
                        alert: "Failed to query NDEF: \(error.localizedDescription)"
                    )
                    return
                }
                switch status {
                case .notSupported:
                    self.finish(session: session, alert: "Tag is not NDEF-compliant.")
                case .readOnly, .readWrite:
                    tag.readNDEF { message, readError in
                        Task { @MainActor in
                            if let readError {
                                self.finish(
                                    session: session,
                                    alert: "Failed to read NDEF: \(readError.localizedDescription)"
                                )
                                return
                            }
                            guard let message else {
                                self.finish(session: session, alert: "Tag returned no NDEF message.")
                                return
                            }
                            let records = self.decode(message)
                            self.lastReadSummary = NFCNDEFCodec.summary(for: records)
                            let alert = "Read \(records.count) record\(records.count == 1 ? "" : "s")."
                            self.finish(session: session, alert: alert)
                        }
                    }
                @unknown default:
                    self.finish(session: session, alert: "Unknown NDEF status.")
                }
            }
        }
    }

    private func write(_ message: NFCNDEFMessage, to tag: NFCNDEFTag, session: NFCNDEFReaderSession) {
        tag.queryNDEFStatus { [weak self] status, capacity, error in
            Task { @MainActor in
                guard let self else { return }
                if let error {
                    self.finish(
                        session: session,
                        alert: "Failed to query NDEF: \(error.localizedDescription)"
                    )
                    return
                }
                switch status {
                case .notSupported:
                    self.finish(session: session, alert: "Tag is not NDEF-compliant.")
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
                    tag.writeNDEF(message) { writeError in
                        Task { @MainActor in
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
