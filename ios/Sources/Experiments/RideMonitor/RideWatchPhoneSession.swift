import Foundation
import WatchConnectivity
import HealthKit

/// Phone-side WatchConnectivity session that pushes live ride snapshots to
/// the companion Watch app, launches it into a frontmost workout session when
/// a ride starts, and receives heart-rate / calorie metrics collected on Watch.
@MainActor
final class RideWatchPhoneSession: NSObject, ObservableObject {
    static let shared = RideWatchPhoneSession()

    /// Latest activity stats mirrored from the Watch workout builder.
    @Published private(set) var latestActivity = RideWatchActivityMetrics.empty

    private var session: WCSession?
    /// Latest snapshot waiting for WCSession activation (ride start can race it).
    private var pendingSnapshot: RideLiveSnapshot?
    private let healthStore = HKHealthStore()
    private var didRequestHealthAuthorization = false
    /// Avoid spamming `startWatchApp` on every 1 Hz snapshot while riding.
    private var didLaunchWatchForCurrentRide = false
    /// Queue at most one authoritative WC `transferUserInfo` start per ride
    /// (ends always transfer so stop isn't lost when unreachable).
    private var didQueueStartTransfer = false

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
        if snapshot.isRiding {
            if !didLaunchWatchForCurrentRide {
                didLaunchWatchForCurrentRide = true
                launchWatchWorkoutIfPossible()
            }
        } else {
            didLaunchWatchForCurrentRide = false
            didQueueStartTransfer = false
        }
    }

    func resetActivity() {
        latestActivity = .empty
    }

    private func flushPending() {
        guard let snapshot = pendingSnapshot else { return }
        guard let session, session.activationState == .activated else { return }

        // Prefer the installed-app check once activated; fall back to paired
        // so we still stage application context before the Watch app launches.
        guard session.isPaired else { return }

        // Watch UI does not render the elevation profile; omit it so we stay
        // under the small application-context budget (~4 KB) and end-of-ride
        // `isRiding: false` is less likely to be dropped.
        var compact = snapshot
        compact.profile = []

        guard let data = try? JSONEncoder().encode(compact),
              let json = try? JSONSerialization.jsonObject(with: data) as? [String: Any] else {
            RideMonitorLog.error("Watch snapshot encode failed")
            return
        }

        let payload: [String: Any] = ["rideLiveSnapshot": json]

        // Application context always delivers the latest snapshot when the
        // Watch wakes; message is best-effort for an immediate UI refresh.
        // transferUserInfo queues authoritative start/stop even when unreachable.
        do {
            try session.updateApplicationContext(payload)
        } catch {
            RideMonitorLog.error("Watch applicationContext failed: \(error.localizedDescription)")
        }
        if session.isReachable {
            session.sendMessage(payload, replyHandler: nil, errorHandler: { error in
                RideMonitorLog.error("Watch sendMessage failed: \(error.localizedDescription)")
            })
        }
        if !snapshot.isRiding {
            session.transferUserInfo(payload)
        } else if !didQueueStartTransfer {
            session.transferUserInfo(payload)
            didQueueStartTransfer = true
        }
        // Keep pending while riding so a later activation / reachability
        // change can re-flush; clear only for the idle end-of-ride snapshot.
        if !snapshot.isRiding {
            pendingSnapshot = nil
        }
    }

    /// Ask watchOS to bring Ride Monitor to the front as a cycling workout so
    /// the user doesn't have to open it manually mid-ride. HealthKit is
    /// required for that frontmost session (any workout type works; cycling
    /// matches this app).
    private func launchWatchWorkoutIfPossible() {
        guard HKHealthStore.isHealthDataAvailable() else { return }
        guard let session, session.isPaired else { return }

        Task {
            await ensureHealthAuthorization()
            let configuration = HKWorkoutConfiguration()
            configuration.activityType = .cycling
            configuration.locationType = .outdoor
            do {
                try await healthStore.startWatchApp(toHandle: configuration)
            } catch {
                // Watch is optional — phone recording continues regardless.
            }
        }
    }

    private func ensureHealthAuthorization() async {
        let workout = HKObjectType.workoutType()
        if healthStore.authorizationStatus(for: workout) == .sharingAuthorized {
            return
        }
        guard !didRequestHealthAuthorization else { return }
        didRequestHealthAuthorization = true
        _ = try? await healthStore.requestAuthorization(toShare: [workout], read: [])
    }

    private func applyActivity(from context: [String: Any]) {
        guard let json = context["rideWatchActivity"] else { return }
        guard JSONSerialization.isValidJSONObject(json),
              let data = try? JSONSerialization.data(withJSONObject: json),
              let decoded = try? JSONDecoder().decode(RideWatchActivityMetrics.self, from: data) else {
            return
        }
        latestActivity = decoded
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
            self.applyActivity(from: session.receivedApplicationContext)
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

    nonisolated func session(_ session: WCSession, didReceiveApplicationContext applicationContext: [String: Any]) {
        Task { @MainActor in
            self.applyActivity(from: applicationContext)
        }
    }

    nonisolated func session(_ session: WCSession, didReceiveMessage message: [String: Any]) {
        Task { @MainActor in
            self.applyActivity(from: message)
        }
    }
    #endif
}
