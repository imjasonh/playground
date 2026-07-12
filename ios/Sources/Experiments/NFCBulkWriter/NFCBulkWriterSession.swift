import CoreNFC
import Foundation

/// Owns a long-lived NDEF reader session that writes the same payload to every
/// tag detected until the user stops (or leaves the experiment).
///
/// CoreNFC delivers delegate callbacks on a session serial queue; `@Published`
/// updates hop to the main queue (same pattern as `ZCameraSession`).
final class NFCBulkWriterSession: NSObject, ObservableObject {
    @Published private(set) var isScanning = false
    @Published private(set) var writtenCount = 0
    @Published private(set) var failedCount = 0
    @Published private(set) var statusMessage = "Set a payload, then start writing."
    @Published private(set) var lastOutcome: String?

    private var readerSession: NFCNDEFReaderSession?
    private var messageToWrite: NFCNDEFMessage?
    private var estimatedPayloadBytes = 0
    private var isHandlingTag = false
    private let stateLock = NSLock()

    var isNFCAvailable: Bool {
        NFCNDEFReaderSession.readingAvailable
    }

    func start(with draft: NFCBulkPayloadDraft) {
        guard !isScanning else { return }

        guard isNFCAvailable else {
            statusMessage = "NFC writing needs a physical iPhone with NFC (not available on Simulator)."
            return
        }

        let message: NFCNDEFMessage
        do {
            message = try NFCBulkNDEFBuilder.message(from: draft)
        } catch {
            statusMessage = error.localizedDescription
            return
        }

        stateLock.lock()
        messageToWrite = message
        estimatedPayloadBytes = NFCBulkNDEFBuilder.estimatedByteCount(of: draft)
        isHandlingTag = false
        stateLock.unlock()

        writtenCount = 0
        failedCount = 0
        lastOutcome = nil

        let session = NFCNDEFReaderSession(
            delegate: self,
            queue: nil,
            invalidateAfterFirstRead: false
        )
        session.alertMessage = "Hold a writable NFC tag near the top of the iPhone."
        readerSession = session
        isScanning = true
        statusMessage = "Ready — tap tags to write. Stop when you’re done."
        session.begin()
    }

    func stop() {
        guard isScanning else { return }
        isScanning = false
        statusMessage = stoppedStatusMessage(cancelled: false)

        stateLock.lock()
        let active = readerSession
        readerSession = nil
        messageToWrite = nil
        estimatedPayloadBytes = 0
        isHandlingTag = false
        stateLock.unlock()

        // Invalidation callback will see isScanning == false and leave our status alone.
        active?.invalidate()
    }

    private func stoppedStatusMessage(cancelled: Bool) -> String {
        let verb = cancelled ? "Cancelled" : "Stopped"
        if writtenCount == 0 && failedCount == 0 {
            return "\(verb). Set a payload and start again anytime."
        }
        return "\(verb) after \(writtenCount) written, \(failedCount) failed."
    }

    private func publishSuccess(session: NFCNDEFReaderSession) {
        DispatchQueue.main.async { [weak self] in
            guard let self else { return }
            self.writtenCount += 1
            self.lastOutcome = "Wrote NDEF payload."
            self.statusMessage = "Wrote tag #\(self.writtenCount). Tap another, or stop."
            session.alertMessage =
                "Wrote \(self.writtenCount) tag\(self.writtenCount == 1 ? "" : "s"). Hold the next tag near the iPhone."
        }
        endTagHandling(session: session)
    }

    private func publishFailure(_ detail: String, session: NFCNDEFReaderSession) {
        DispatchQueue.main.async { [weak self] in
            guard let self else { return }
            self.failedCount += 1
            self.lastOutcome = detail
            self.statusMessage = detail
            session.alertMessage = detail
        }
        endTagHandling(session: session)
    }

    private func endTagHandling(session: NFCNDEFReaderSession) {
        stateLock.lock()
        isHandlingTag = false
        stateLock.unlock()
        session.restartPolling()
    }

    private func takeWriteContext() -> (message: NFCNDEFMessage, bytes: Int)? {
        stateLock.lock()
        defer { stateLock.unlock() }
        guard !isHandlingTag, let message = messageToWrite else { return nil }
        isHandlingTag = true
        return (message, estimatedPayloadBytes)
    }
}

extension NFCBulkWriterSession: NFCNDEFReaderSessionDelegate {
    func readerSessionDidBecomeActive(_ session: NFCNDEFReaderSession) {}

    func readerSession(_ session: NFCNDEFReaderSession, didInvalidateWithError error: Error) {
        stateLock.lock()
        readerSession = nil
        messageToWrite = nil
        estimatedPayloadBytes = 0
        isHandlingTag = false
        stateLock.unlock()

        DispatchQueue.main.async { [weak self] in
            guard let self else { return }
            let wasScanning = self.isScanning
            self.isScanning = false
            guard wasScanning else { return }

            let nsError = error as NSError
            if nsError.domain == NFCReaderError.errorDomain {
                let code = nsError.code
                if code == NFCReaderError.readerSessionInvalidationErrorUserCanceled.rawValue {
                    self.statusMessage = self.stoppedStatusMessage(cancelled: true)
                    return
                }
                if code == NFCReaderError.readerSessionInvalidationErrorFirstNDEFTagRead.rawValue {
                    self.statusMessage = self.stoppedStatusMessage(cancelled: false)
                    return
                }
            }
            self.statusMessage = error.localizedDescription
        }
    }

    func readerSession(_ session: NFCNDEFReaderSession, didDetectNDEFs messages: [NFCNDEFMessage]) {
        // Writing uses didDetect(tags:). Ignore pure-read callbacks.
    }

    func readerSession(_ session: NFCNDEFReaderSession, didDetect tags: [NFCNDEFTag]) {
        if tags.count > 1 {
            session.alertMessage = "More than one tag detected. Hold a single tag."
            session.restartPolling()
            return
        }

        guard let tag = tags.first else {
            session.restartPolling()
            return
        }

        guard let context = takeWriteContext() else {
            session.restartPolling()
            return
        }

        session.connect(to: tag) { [weak self] connectError in
            guard let self else { return }
            if let connectError {
                self.publishFailure(
                    "Couldn’t connect: \(connectError.localizedDescription)",
                    session: session
                )
                return
            }

            tag.queryNDEFStatus { status, capacity, queryError in
                if let queryError {
                    self.publishFailure(
                        "Couldn’t query tag: \(queryError.localizedDescription)",
                        session: session
                    )
                    return
                }

                switch status {
                case .notSupported:
                    self.publishFailure("Tag doesn’t support NDEF.", session: session)
                case .readOnly:
                    self.publishFailure("Tag is read-only.", session: session)
                case .readWrite:
                    if capacity > 0 && context.bytes > capacity {
                        self.publishFailure("Tag too small (\(capacity) bytes).", session: session)
                        return
                    }
                    tag.writeNDEF(context.message) { writeError in
                        if let writeError {
                            self.publishFailure(
                                "Write failed: \(writeError.localizedDescription)",
                                session: session
                            )
                        } else {
                            self.publishSuccess(session: session)
                        }
                    }
                @unknown default:
                    self.publishFailure("Unknown NDEF status.", session: session)
                }
            }
        }
    }
}
