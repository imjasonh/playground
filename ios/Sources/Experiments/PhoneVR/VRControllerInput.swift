import CoreHaptics
import GameController
import QuartzCore
import simd

/// The active game controller as the render thread sees it.
struct VRControllerSnapshot {
    var name: String?
    var leftStick: SIMD2<Float> = .zero
    var rightStick: SIMD2<Float> = .zero
    /// Press counts per button. Comparing with the previous read finds new
    /// presses even when a press and release both happen between frames.
    var presses: [VRControllerButton: Int] = [:]
    /// Controller rotation since the last pointer recenter, in the
    /// controller's own frame, or nil without motion sensors.
    var pointerDelta: simd_quatf?
}

/// Reads an extended gamepad (Xbox, DualSense, Joy-Con) on GameController's
/// handler queue and mirrors it into a snapshot for the render thread.
final class VRControllerInput: @unchecked Sendable {
    private let handlerQueue = DispatchQueue(label: "PhoneVR.controller", qos: .userInteractive)
    private let snapshotBox = VRLocked(VRControllerSnapshot())
    private let active = VRLocked<GCController?>(nil)
    private let pointer = VRLocked<simd_quatf?>(nil)
    private var observers: [NSObjectProtocol] = []
    private var lastMotionTime: CFTimeInterval?
    private var hapticEngine: CHHapticEngine?

    func start() {
        let center = NotificationCenter.default
        observers.append(center.addObserver(forName: .GCControllerDidConnect, object: nil, queue: .main) { [weak self] note in
            guard let controller = note.object as? GCController else { return }
            self?.attach(controller)
        })
        observers.append(center.addObserver(forName: .GCControllerDidDisconnect, object: nil, queue: .main) { [weak self] note in
            guard let controller = note.object as? GCController else { return }
            self?.detach(controller)
        })
        if let controller = GCController.current ?? GCController.controllers().first {
            attach(controller)
        }
    }

    func stop() {
        for observer in observers {
            NotificationCenter.default.removeObserver(observer)
        }
        observers.removeAll()
        if let controller = active.get() { detach(controller) }
    }

    func snapshot() -> VRControllerSnapshot {
        var snapshot = snapshotBox.get()
        snapshot.pointerDelta = pointer.get()
        return snapshot
    }

    /// Makes the controller's current orientation the pointer's forward.
    func recenterPointer() {
        pointer.withLock { current in
            if current != nil { current = VRMath.identityRotation }
        }
    }

    /// A short click on the controller's haptics, if it has them.
    func playTap() {
        handlerQueue.async { [weak self] in
            guard let self, let controller = self.active.get() else { return }
            if self.hapticEngine == nil {
                self.hapticEngine = controller.haptics?.createEngine(withLocality: .default)
                try? self.hapticEngine?.start()
            }
            guard let engine = self.hapticEngine else { return }
            let event = CHHapticEvent(
                eventType: .hapticTransient,
                parameters: [
                    CHHapticEventParameter(parameterID: .hapticIntensity, value: 0.6),
                    CHHapticEventParameter(parameterID: .hapticSharpness, value: 0.8),
                ],
                relativeTime: 0
            )
            guard let pattern = try? CHHapticPattern(events: [event], parameters: []) else { return }
            try? engine.makePlayer(with: pattern).start(atTime: CHHapticTimeImmediate)
        }
    }

    private func attach(_ controller: GCController) {
        guard let gamepad = controller.extendedGamepad else { return }
        if let previous = active.get(), previous !== controller { detach(previous) }
        active.set(controller)
        controller.handlerQueue = handlerQueue
        snapshotBox.withLock { $0.name = controller.vendorName ?? "Game controller" }

        let buttons: [(GCControllerButtonInput?, VRControllerButton)] = [
            (gamepad.buttonA, .a), (gamepad.buttonB, .b), (gamepad.buttonX, .x), (gamepad.buttonY, .y),
            (gamepad.buttonMenu, .menu), (gamepad.buttonOptions, .options),
            (gamepad.dpad.up, .dpadUp), (gamepad.dpad.down, .dpadDown),
            (gamepad.dpad.left, .dpadLeft), (gamepad.dpad.right, .dpadRight),
            (gamepad.leftShoulder, .leftShoulder), (gamepad.rightShoulder, .rightShoulder),
        ]
        for (input, button) in buttons {
            input?.pressedChangedHandler = { [weak self] _, _, pressed in
                guard pressed else { return }
                self?.snapshotBox.withLock { $0.presses[button, default: 0] += 1 }
            }
        }
        gamepad.leftThumbstick.valueChangedHandler = { [weak self] _, x, y in
            self?.snapshotBox.withLock { $0.leftStick = SIMD2(x, y) }
        }
        gamepad.rightThumbstick.valueChangedHandler = { [weak self] _, x, y in
            self?.snapshotBox.withLock { $0.rightStick = SIMD2(x, y) }
        }
        if let motion = controller.motion, motion.hasRotationRate {
            if motion.sensorsRequireManualActivation { motion.sensorsActive = true }
            pointer.set(VRMath.identityRotation)
            motion.valueChangedHandler = { [weak self] motion in
                self?.integrate(motion)
            }
        }
    }

    private func detach(_ controller: GCController) {
        guard active.get() === controller else { return }
        if let gamepad = controller.extendedGamepad {
            for input in [gamepad.buttonA, gamepad.buttonB, gamepad.buttonX, gamepad.buttonY, gamepad.buttonMenu,
                          gamepad.dpad.up, gamepad.dpad.down, gamepad.dpad.left, gamepad.dpad.right,
                          gamepad.leftShoulder, gamepad.rightShoulder] {
                input.pressedChangedHandler = nil
            }
            gamepad.buttonOptions?.pressedChangedHandler = nil
            gamepad.leftThumbstick.valueChangedHandler = nil
            gamepad.rightThumbstick.valueChangedHandler = nil
        }
        if let motion = controller.motion {
            motion.valueChangedHandler = nil
            if motion.sensorsRequireManualActivation { motion.sensorsActive = false }
        }
        active.set(nil)
        pointer.set(nil)
        snapshotBox.set(VRControllerSnapshot())
        handlerQueue.async { [weak self] in
            self?.hapticEngine?.stop()
            self?.hapticEngine = nil
            self?.lastMotionTime = nil
        }
    }

    /// Runs on the handler queue.
    private func integrate(_ motion: GCMotion) {
        let now = CACurrentMediaTime()
        let dt = lastMotionTime.map { Float(min(now - $0, 0.05)) } ?? 0
        lastMotionTime = now
        let r = motion.rotationRate
        let rate = SIMD3<Float>(Float(r.x), Float(r.y), Float(r.z))
        pointer.withLock { current in
            guard let attitude = current else { return }
            current = VRMath.integrate(attitude, bodyRate: rate, dt: dt)
        }
    }
}
