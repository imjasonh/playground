import Metal
import QuartzCore
import SwiftUI
import UIKit

/// Everything one trip into the headset needs, handed over at presentation.
struct VRLaunchRequest: Identifiable {
    let id = UUID()
    let settings: PhoneVRSettings
    let device: PhoneVRDeviceInfo
}

/// Full-screen landscape host for the VR renderer.
///
/// SwiftUI can't lock one screen's orientation, so the headset view is a
/// UIKit controller presented full screen: its supported orientation is the
/// one landscape that matches how the phone sits in the viewer. It also hides
/// the status bar and home indicator and defers edge swipes, since the
/// screen is inside the viewer.
final class VRViewController: UIViewController {
    private let request: VRLaunchRequest
    private let onFinish: (VRSessionResult?) -> Void
    private let metalLayer = CAMetalLayer()
    private var session: VRSession?
    private var finished = false

    init(request: VRLaunchRequest, onFinish: @escaping (VRSessionResult?) -> Void) {
        self.request = request
        self.onFinish = onFinish
        super.init(nibName: nil, bundle: nil)
        modalPresentationStyle = .fullScreen
    }

    required init?(coder: NSCoder) {
        nil
    }

    private var orientation: UIInterfaceOrientation {
        request.settings.mounting == .cameraLeft ? .landscapeRight : .landscapeLeft
    }

    override var supportedInterfaceOrientations: UIInterfaceOrientationMask {
        orientation == .landscapeRight ? .landscapeRight : .landscapeLeft
    }

    override var preferredInterfaceOrientationForPresentation: UIInterfaceOrientation { orientation }
    override var prefersStatusBarHidden: Bool { true }
    override var prefersHomeIndicatorAutoHidden: Bool { true }
    override var preferredScreenEdgesDeferringSystemGestures: UIRectEdge { .all }

    override func viewDidLoad() {
        super.viewDidLoad()
        view.backgroundColor = .black
        // Off by default, which would hide the second finger from the exit gesture.
        view.isMultipleTouchEnabled = true
        view.layer.addSublayer(metalLayer)
        view.isAccessibilityElement = true
        view.accessibilityLabel = "Phone VR"
        view.accessibilityIdentifier = "phoneVRView"
        view.accessibilityCustomActions = [
            UIAccessibilityCustomAction(name: "Exit VR") { [weak self] _ in
                self?.close()
                return true
            },
        ]

        let twoFingerTap = UITapGestureRecognizer(target: self, action: #selector(handleTwoFingerTap))
        twoFingerTap.numberOfTouchesRequired = 2
        let tap = UITapGestureRecognizer(target: self, action: #selector(handleTap))
        tap.require(toFail: twoFingerTap)
        let longPress = UILongPressGestureRecognizer(target: self, action: #selector(handleLongPress(_:)))
        longPress.minimumPressDuration = 0.8
        view.addGestureRecognizer(twoFingerTap)
        view.addGestureRecognizer(tap)
        view.addGestureRecognizer(longPress)
    }

    override func viewDidLayoutSubviews() {
        super.viewDidLayoutSubviews()
        CATransaction.begin()
        CATransaction.setDisableActions(true)
        metalLayer.frame = view.bounds
        CATransaction.commit()
        metalLayer.contentsScale = view.window?.windowScene?.screen.nativeScale ?? traitCollection.displayScale
        // One drawable pixel per panel pixel, whatever the point size says.
        metalLayer.drawableSize = CGSize(width: request.device.screen.widthPixels, height: request.device.screen.heightPixels)
    }

    override func viewDidAppear(_ animated: Bool) {
        super.viewDidAppear(animated)
        UIApplication.shared.isIdleTimerDisabled = true
        startSession()
    }

    override func viewWillDisappear(_ animated: Bool) {
        super.viewWillDisappear(animated)
        UIApplication.shared.isIdleTimerDisabled = false
    }

    override func accessibilityPerformEscape() -> Bool {
        close()
        return true
    }

    private func startSession() {
        guard session == nil, !finished else { return }
        guard let device = MTLCreateSystemDefaultDevice() else {
            showError("This device has no Metal GPU.")
            return
        }
        do {
            var options = VRRenderer.Options()
            options.multisample = request.settings.multisampling
            options.singlePassStereo = request.settings.singlePassStereo
            #if targetEnvironment(simulator)
            options.memorylessTargets = false
            #endif
            let renderer = try VRRenderer(device: device, options: options)
            metalLayer.device = device
            metalLayer.pixelFormat = VRRenderer.drawableFormat
            metalLayer.framebufferOnly = true
            metalLayer.maximumDrawableCount = 3
            metalLayer.developerHUDProperties = request.settings.metalPerformanceHUD ? ["mode": "default", "logging": "default"] : nil
            let configuration = VRSessionConfiguration(settings: request.settings, screen: request.device.screen, model: request.device.model)
            let session = VRSession(configuration: configuration, renderer: renderer, layer: metalLayer)
            session.onExitRequested = { [weak self] in self?.close() }
            self.session = session
            session.start()
        } catch {
            showError(error.localizedDescription)
        }
    }

    private func showError(_ text: String) {
        let label = UILabel()
        label.text = text
        label.textColor = .white
        label.font = .preferredFont(forTextStyle: .headline)
        label.adjustsFontForContentSizeCategory = true
        label.numberOfLines = 0
        label.textAlignment = .center
        let button = UIButton(configuration: .filled(), primaryAction: UIAction(title: "Close") { [weak self] _ in self?.close() })
        let stack = UIStackView(arrangedSubviews: [label, button])
        stack.axis = .vertical
        stack.spacing = 16
        stack.alignment = .center
        stack.translatesAutoresizingMaskIntoConstraints = false
        view.addSubview(stack)
        NSLayoutConstraint.activate([
            stack.centerXAnchor.constraint(equalTo: view.centerXAnchor),
            stack.centerYAnchor.constraint(equalTo: view.centerYAnchor),
            stack.widthAnchor.constraint(lessThanOrEqualTo: view.widthAnchor, multiplier: 0.8),
        ])
    }

    @objc private func handleTap() {
        session?.send(.tap)
    }

    @objc private func handleTwoFingerTap() {
        close()
    }

    @objc private func handleLongPress(_ recognizer: UILongPressGestureRecognizer) {
        if recognizer.state == .began { session?.send(.longPress) }
    }

    /// Dismisses at once and reports the session's result when its render
    /// thread stops. Leaving the headset never waits on teardown. If no result
    /// arrives within a second of the dismissal, the report goes out empty.
    func close() {
        guard !finished else { return }
        finished = true
        let report = VRFinishReport(onFinish)
        if let session {
            session.stop { result in report.send(result) }
        } else {
            report.send(nil)
        }
        dismiss(animated: true) {
            DispatchQueue.main.asyncAfter(deadline: .now() + 1) { report.send(nil) }
        }
    }
}

/// Calls `onFinish` once, with whichever result arrives first. Main thread only.
private final class VRFinishReport {
    private var onFinish: ((VRSessionResult?) -> Void)?

    init(_ onFinish: @escaping (VRSessionResult?) -> Void) {
        self.onFinish = onFinish
    }

    func send(_ result: VRSessionResult?) {
        let callback = onFinish
        onFinish = nil
        callback?(result)
    }
}

/// Presents `VRViewController` from SwiftUI when `request` is set, and clears
/// it when the session ends.
struct VRPresenter: UIViewControllerRepresentable {
    @Binding var request: VRLaunchRequest?
    var onFinish: (VRSessionResult?) -> Void

    final class Coordinator {
        var presentedID: UUID?
    }

    func makeCoordinator() -> Coordinator {
        Coordinator()
    }

    func makeUIViewController(context: Context) -> UIViewController {
        UIViewController()
    }

    func updateUIViewController(_ host: UIViewController, context: Context) {
        guard let request, context.coordinator.presentedID != request.id else { return }
        context.coordinator.presentedID = request.id
        let binding = $request
        let finish = onFinish
        // Present after this SwiftUI update finishes.
        Task { @MainActor in
            let controller = VRViewController(request: request) { result in
                binding.wrappedValue = nil
                finish(result)
            }
            host.present(controller, animated: true)
        }
    }
}
