import Foundation
import WatchConnectivity

/// Watch-side session that receives `RideLiveSnapshot` updates from the phone.
@MainActor
final class RideWatchReceiver: NSObject, ObservableObject {
    static let shared = RideWatchReceiver()

    @Published private(set) var snapshot: RideLiveSnapshot = .idle

    private var session: WCSession?

    private override init() {
        super.init()
        guard WCSession.isSupported() else { return }
        let session = WCSession.default
        self.session = session
        session.delegate = self
        session.activate()
        // Best-effort early read; the authoritative load is in
        // `activationDidCompleteWith`, once the session is actually ready.
        apply(context: session.receivedApplicationContext)
    }

    private func apply(context: [String: Any]) {
        guard let json = context["rideLiveSnapshot"] else { return }
        guard JSONSerialization.isValidJSONObject(json),
              let data = try? JSONSerialization.data(withJSONObject: json),
              let decoded = try? JSONDecoder().decode(RideLiveSnapshot.self, from: data) else {
            return
        }
        snapshot = decoded
    }
}

extension RideWatchReceiver: WCSessionDelegate {
    nonisolated func session(
        _ session: WCSession,
        activationDidCompleteWith activationState: WCSessionActivationState,
        error: Error?
    ) {
        Task { @MainActor in
            // Application context is reliable only after activation completes.
            self.apply(context: session.receivedApplicationContext)
        }
    }

    nonisolated func session(_ session: WCSession, didReceiveApplicationContext applicationContext: [String: Any]) {
        Task { @MainActor in
            self.apply(context: applicationContext)
        }
    }

    nonisolated func session(_ session: WCSession, didReceiveMessage message: [String: Any]) {
        Task { @MainActor in
            self.apply(context: message)
        }
    }
}
