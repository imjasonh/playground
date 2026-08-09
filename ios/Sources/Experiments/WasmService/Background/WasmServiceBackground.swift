import Foundation

#if canImport(BackgroundTasks)
    import BackgroundTasks
#endif
#if canImport(UIKit)
    import UIKit
#endif

/// Keeps the service running for as long as iOS is willing to let it, and is
/// honest about how long that is.
///
/// **There is no way for an App Store app to run a server permanently in the
/// background.** Nothing here works around that, because nothing can. What iOS
/// offers is three windows, and this uses all three:
///
/// - **Foreground.** Unlimited. With the idle timer disabled and the phone on
///   a charger, this is the "leave it running" mode, and it is the only one
///   that is genuinely continuous.
/// - **A background assertion.** About thirty seconds after the app leaves the
///   foreground, requested so a request already in flight is not cut off.
/// - **`BGProcessingTask`.** Minutes at a time, scheduled by the system rather
///   than by us, and — because this asks for it — only while charging. Each
///   window schedules the next, so a plugged-in phone comes back periodically
///   rather than once.
///
/// The paths that *would* run indefinitely are all closed. A `NEPacketTunnel`
/// or `NEAppPushProvider` needs a Network Extension entitlement Apple grants
/// case by case, and would run the code in the extension rather than the app.
/// The `audio` and `location` background modes do keep an app alive, and this
/// app already declares both for Snore Log and Ride Monitor — playing silent
/// audio to keep a web server up would be a straightforward way to get the
/// whole app rejected, so it is not done here.
@MainActor
final class WasmServiceBackground: ObservableObject {
    /// Also listed under `BGTaskSchedulerPermittedIdentifiers` in the app's
    /// Info.plist; registration fails silently if the two ever disagree.
    static let taskIdentifier = "io.github.imjasonh.playground.wasmservice.window"

    static let shared = WasmServiceBackground()

    /// What the user asked for. Persisted, because the point is to survive the
    /// app being backgrounded and relaunched.
    @Published var keepAliveEnabled: Bool {
        didSet {
            UserDefaults.standard.set(keepAliveEnabled, forKey: Self.keepAliveKey)
            if keepAliveEnabled {
                scheduleNextWindow()
            } else {
                cancelScheduledWindows()
            }
        }
    }

    /// Keeps the screen — and so the app — awake while serving. The single
    /// most effective thing available, and the reason "plugged into power" is
    /// the right way to run this.
    @Published var staysAwakeInForeground: Bool = false {
        didSet { applyIdleTimer() }
    }

    @Published private(set) var windowsRun = 0
    @Published private(set) var lastWindowStarted: Date?
    @Published private(set) var lastSchedulingError: String?

    /// Set by the model while a service is running; the background window has
    /// to be able to bring the service back up after a relaunch.
    var resumeService: (() async -> Bool)?

    private static let keepAliveKey = "wasmservice.keepAlive"
    private var registered = false
    #if canImport(UIKit)
        private var assertion: UIBackgroundTaskIdentifier = .invalid
    #endif

    private init() {
        keepAliveEnabled = UserDefaults.standard.bool(forKey: Self.keepAliveKey)
    }

    // MARK: - Launch

    /// Must run before the app finishes launching — `BGTaskScheduler` refuses
    /// registrations after that, and the failure is a crash on the next
    /// submit rather than an error here.
    func registerLaunchHandler() {
        #if canImport(BackgroundTasks)
            guard !registered else { return }
            registered = BGTaskScheduler.shared.register(
                forTaskWithIdentifier: Self.taskIdentifier,
                using: nil
            ) { [weak self] task in
                guard let processing = task as? BGProcessingTask else {
                    task.setTaskCompleted(success: false)
                    return
                }
                // BGTaskScheduler calls this off the main actor, and hopping
                // is the only option that compiles below iOS 17
                // (`MainActor.assumeIsolated` is 17+).
                Task { @MainActor in
                    self?.runWindow(processing)
                }
            }
        #endif
    }

    // MARK: - Windows

    #if canImport(BackgroundTasks)
        private func runWindow(_ task: BGProcessingTask) {
            windowsRun += 1
            lastWindowStarted = Date()
            // Chain immediately: the system decides when the next window
            // happens, and a request submitted at the end of this one is the
            // only way to ask for another.
            scheduleNextWindow()

            let work = Task { @MainActor in
                let resumed = await self.resumeService?() ?? false
                // Nothing to poll for — the service either came up and is now
                // answering requests for as long as this window lasts, or it
                // did not. Sleeping here is what keeps the window open.
                if resumed {
                    try? await Task.sleep(nanoseconds: 25 * 60 * 1_000_000_000)
                }
                task.setTaskCompleted(success: resumed)
            }

            task.expirationHandler = {
                work.cancel()
            }
        }
    #endif

    func scheduleNextWindow() {
        #if canImport(BackgroundTasks)
            guard keepAliveEnabled, registered else { return }
            let request = BGProcessingTaskRequest(identifier: Self.taskIdentifier)
            // "Only while plugged in" is a real setting, not a euphemism: iOS
            // will hold the window back until the phone is charging.
            request.requiresExternalPower = true
            request.requiresNetworkConnectivity = true
            request.earliestBeginDate = Date(timeIntervalSinceNow: 60)
            do {
                try BGTaskScheduler.shared.submit(request)
                lastSchedulingError = nil
            } catch {
                lastSchedulingError = error.localizedDescription
            }
        #endif
    }

    func cancelScheduledWindows() {
        #if canImport(BackgroundTasks)
            BGTaskScheduler.shared.cancel(taskRequestWithIdentifier: Self.taskIdentifier)
        #endif
    }

    // MARK: - Leaving the foreground

    /// Buys the ~30 seconds iOS grants on the way to suspension, so a request
    /// that is mid-flight when the user swipes away still gets an answer.
    func beginShortAssertion() {
        #if canImport(UIKit)
            guard assertion == .invalid else { return }
            // iOS allows a few seconds' grace after calling the expiration
            // handler, which is what makes the hop to the main actor safe.
            assertion = UIApplication.shared.beginBackgroundTask(withName: "wasm-service-drain") { [weak self] in
                Task { @MainActor in self?.endShortAssertion() }
            }
        #endif
    }

    func endShortAssertion() {
        #if canImport(UIKit)
            guard assertion != .invalid else { return }
            UIApplication.shared.endBackgroundTask(assertion)
            assertion = .invalid
        #endif
    }

    private func applyIdleTimer() {
        #if canImport(UIKit)
            UIApplication.shared.isIdleTimerDisabled = staysAwakeInForeground
        #endif
    }
}
