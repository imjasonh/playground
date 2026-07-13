import Foundation
import WatchConnectivity

/// Phone-side WatchConnectivity session that pushes live ride snapshots to
/// the companion Watch app. Recording stays on the phone; the Watch is a
/// glanceable remote display.
@MainActor
final class RideWatchPhoneSession: NSObject, ObservableObject {
    static let shared = RideWatchPhoneSession()

    private var session: WCSession?
    /// Latest snapshot waiting for WCSession activation (ride start can race it).
    private var pendingSnapshot: RideLiveSnapshot?

    private override init() {
        super.init()
        guard WCSession.isSupported() else { return }
        let session = WCSession.default
        self.session = session
        session.delegate = self
        session.activate()
    }

    func send(_ snapshot: RideLiveSnapshot) {
        pendingSnapshot = snapshot
        flushPending()
    }

    private func flushPending() {
        guard let snapshot = pendingSnapshot else { return }
        guard let session, session.activationState == .activated else { return }

        // Prefer the installed-app check once activated; fall back to paired
        // so we still stage application context before the Watch app launches.
        guard session.isPaired else { return }

        guard let data = try? JSONEncoder().encode(snapshot),
              let json = try? JSONSerialization.jsonObject(with: data) as? [String: Any] else {
            return
        }

        let payload: [String: Any] = ["rideLiveSnapshot": json]

        // Application context always delivers the latest snapshot when the
        // Watch wakes; message is best-effort for an immediate UI refresh.
        try? session.updateApplicationContext(payload)
        if session.isReachable {
            session.sendMessage(payload, replyHandler: nil, errorHandler: { _ in })
        }
        // Keep pending while riding so a later activation / reachability
        // change can re-flush; clear only for the idle end-of-ride snapshot.
        if !snapshot.isRiding {
            pendingSnapshot = nil
        }
    }
}

extension RideWatchPhoneSession: WCSessionDelegate {
    nonisolated func session(
        _ session: WCSession,
        activationDidCompleteWith activationState: WCSessionActivationState,
        error: Error?
    ) {
        Task { @MainActor in
            self.flushPending()
        }
    }

    #if os(iOS)
    nonisolated func sessionDidBecomeInactive(_ session: WCSession) {}
    nonisolated func sessionDidDeactivate(_ session: WCSession) {
        session.activate()
    }

    nonisolated func sessionReachabilityDidChange(_ session: WCSession) {
        Task { @MainActor in
            self.flushPending()
        }
    }
    #endif
}
