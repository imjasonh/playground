import Foundation
import WatchConnectivity

/// Watch-side session that receives `RideLiveSnapshot` updates from the phone,
/// keeps an `HKWorkoutSession` in sync so the companion stays frontmost, and
/// sends heart-rate / calorie metrics back to the phone.
@MainActor
final class RideWatchReceiver: NSObject, ObservableObject {
    static let shared = RideWatchReceiver()

    @Published private(set) var snapshot: RideLiveSnapshot = .idle

    private var session: WCSession?
    private let workout = RideWatchWorkoutController.shared
    /// Guards against a late `isRiding: true` message restarting a workout
    /// after the phone already sent the end-of-ride snapshot.
    private var lastAppliedStartedAt: Date = .distantPast
    private var lastAppliedIsRiding = false

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

    /// Push the latest Watch activity stats to the phone (best-effort).
    func sendActivity(_ metrics: RideWatchActivityMetrics) {
        guard let session, session.activationState == .activated else { return }
        guard let data = try? JSONEncoder().encode(metrics),
              let json = try? JSONSerialization.jsonObject(with: data) as? [String: Any] else {
            return
        }
        let payload: [String: Any] = ["rideWatchActivity": json]
        // Application context delivers the latest values when the phone next
        // wakes the session; message is for an immediate UI refresh.
        try? session.updateApplicationContext(payload)
        if session.isReachable {
            session.sendMessage(payload, replyHandler: nil, errorHandler: { _ in })
        }
    }

    private func apply(context: [String: Any]) {
        guard let json = context["rideLiveSnapshot"] else { return }
        guard JSONSerialization.isValidJSONObject(json),
              let data = try? JSONSerialization.data(withJSONObject: json),
              let decoded = try? JSONDecoder().decode(RideLiveSnapshot.self, from: data) else {
            return
        }

        if decoded.isRiding {
            // Ignore a stale start for an older ride after we've already ended.
            if !lastAppliedIsRiding,
               decoded.startedAt < lastAppliedStartedAt {
                return
            }
            // Same ride, already riding — still refresh UI/metrics.
        } else if lastAppliedIsRiding,
                  decoded.startedAt < lastAppliedStartedAt {
            // Stale end for a previous ride while a newer one is active.
            return
        }

        lastAppliedStartedAt = max(lastAppliedStartedAt, decoded.startedAt)
        lastAppliedIsRiding = decoded.isRiding
        snapshot = decoded
        workout.sync(isRiding: decoded.isRiding, startedAt: decoded.startedAt)
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

    nonisolated func session(_ session: WCSession, didReceiveUserInfo userInfo: [String: Any] = [:]) {
        Task { @MainActor in
            self.apply(context: userInfo)
        }
    }
}
