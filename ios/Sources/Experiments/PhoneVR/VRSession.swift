import Darwin
import Foundation
import Metal
import QuartzCore
import simd

/// Inputs fixed for one trip into the headset.
struct VRSessionConfiguration {
    var settings: PhoneVRSettings
    var screen: VRPhoneScreen
    var model: VRPhoneModel
}

/// What a session reports when it ends.
struct VRSessionResult {
    var summary: VRSessionSummary
    /// The viewer profile after any in-headset calibration.
    var profile: VRViewerProfile
}

enum VRSessionCommand: Equatable {
    /// A tap on the screen: select, or skip the countdown.
    case tap
    case longPress
}

/// Sleeps the render thread with sub-millisecond precision.
private enum VRClock {
    static let timebase: mach_timebase_info_data_t = {
        var info = mach_timebase_info_data_t()
        mach_timebase_info(&info)
        return info
    }()

    static func wait(seconds: TimeInterval) {
        guard seconds > 0, timebase.numer > 0 else { return }
        let ticks = UInt64(seconds * 1e9 * Double(timebase.denom) / Double(timebase.numer))
        mach_wait_until(mach_absolute_time() + ticks)
    }
}

/// One VR session: sensors, input, audio, and the render loop.
///
/// The render loop runs on its own thread, driven by a `CAMetalDisplayLink`
/// on that thread's run loop. Each frame it reads the newest sensor data,
/// predicts the head pose for the moment the frame lights up, renders both
/// eyes, waits until just before the GPU frees up, reads the gyro again, and
/// encodes the lens-correction pass with a rotation that makes up the
/// difference. Everything under "Render thread" is touched only on that thread.
final class VRSession: NSObject, CAMetalDisplayLinkDelegate, @unchecked Sendable {
    private let configuration: VRSessionConfiguration
    private let settings: PhoneVRSettings
    private let renderer: VRRenderer
    private let layer: CAMetalLayer
    private let tracking = VRTrackingSource()
    private let controllers = VRControllerInput()
    private let audio = VRAudio()
    private let airPods: VRHeadphoneMotionSource?
    private let painter: VRPanelPainter
    private let cameraTextures: VRCameraTextureCache

    private let commands = VRLocked<[VRSessionCommand]>([])
    private let stopRequested = VRLocked(false)
    private let statistics = VRLocked(VRFrameStatistics())
    private let gpuTimes = VRLocked((eye: VRSmoothedValue(smoothing: 0.1), final: VRSmoothedValue(smoothing: 0.1)))
    private let profileBox: VRLocked<VRViewerProfile>
    private let slipBox = VRLocked(0)
    private let worldTrackingBox = VRLocked(false)

    /// Main thread only.
    private var completion: ((VRSessionResult) -> Void)?
    /// Called on the main thread when the wearer picks Exit in the headset.
    var onExitRequested: (() -> Void)?

    // MARK: Render thread

    private var displayLink: CAMetalDisplayLink?
    private var tracker: VRHeadTracker
    private var playSpace = VRPlaySpace()
    private var experience: VRExperience
    private var dwell = VRGazeDwell<VRGazeTarget>()
    private var governor: VRFrameGovernor
    private var lateLatch = VRLateLatch()
    private var layout: VRStereoLayout
    private var sessionStart: TimeInterval?
    private var lastFrameTime: TimeInterval?
    private var lastTrackingTimestamp: TimeInterval = -1
    private var lastMotionTimestamp: TimeInterval = -1
    private var lastTrackingArrival: TimeInterval?
    private var floorApplied = false
    private var seenPresses: [VRControllerButton: Int] = [:]
    private var snapArmed = true
    private var message: (text: String, until: TimeInterval)?
    private var passthroughOpacity: Float = 0
    private var vignette: Float = 1
    private var lastMode: VRTrackingMode?
    private var pointerHeading: Float = 0
    private var thermal: VRThermalLevel = .nominal
    private var lowPower = false
    private var lastPowerCheck: TimeInterval = -1
    private var statsLines: [String] = ["Measuring…"]
    private var lastStatsUpdate: TimeInterval = -1
    private var lastSlips = 0
    private var lastLatchWait: TimeInterval = 0
    private var lastHead: VRHeadPose?

    init(configuration: VRSessionConfiguration, renderer: VRRenderer, layer: CAMetalLayer) {
        self.configuration = configuration
        let settings = configuration.settings
        self.settings = settings
        self.renderer = renderer
        self.layer = layer
        painter = VRPanelPainter(device: renderer.device)
        cameraTextures = VRCameraTextureCache(device: renderer.device)
        airPods = settings.airPodsCrossCheck ? VRHeadphoneMotionSource(ownsPhoneMotion: false) : nil
        let frames = VRDeviceFrames(mounting: settings.mounting, rearCameraOffset: configuration.model.rearCameraOffset)
        var trackerConfiguration = VRHeadTracker.Configuration(frames: frames)
        trackerConfiguration.predictionEnabled = settings.prediction
        tracker = VRHeadTracker(configuration: trackerConfiguration)
        layout = VRStereoLayout(screen: configuration.screen, profile: settings.profile)
        var experience = VRExperience(
            profile: settings.profile,
            countdown: settings.countdownSeconds,
            passthroughAvailable: false,
            showStats: settings.showStats
        )
        experience.snapTurnAngle = VRMath.radians(settings.snapTurnDegrees)
        self.experience = experience
        governor = VRFrameGovernor(configuration: settings.governorConfiguration())
        profileBox = VRLocked(settings.profile)
        super.init()
        playSpace.fallbackEyeHeight = settings.eyeHeight
        playSpace.boundaryRadius = settings.playAreaRadius
        lateLatch.enabled = settings.lateLatch
    }

    // MARK: - Main thread

    func start() {
        let worldTracking = settings.tracking == .sixDoF && VRTrackingSource.supportsWorldTracking
        worldTrackingBox.set(worldTracking)
        tracking.start(worldTracking: worldTracking)
        controllers.start()
        if settings.spatialAudio { audio.start() }
        airPods?.start()
        let thread = Thread { [weak self] in self?.runRenderLoop() }
        thread.name = "PhoneVR render"
        thread.qualityOfService = .userInteractive
        thread.start()
    }

    /// Stops the render loop and sensors, then calls `completion` on the main thread.
    func stop(completion: @escaping (VRSessionResult) -> Void) {
        self.completion = completion
        stopRequested.set(true)
    }

    func send(_ command: VRSessionCommand) {
        commands.withLock { $0.append(command) }
    }

    private func finish(_ result: VRSessionResult) {
        tracking.stop()
        controllers.stop()
        audio.stop()
        airPods?.stop()
        cameraTextures.flush()
        completion?(result)
        completion = nil
    }

    // MARK: - Render loop

    private func runRenderLoop() {
        let link = CAMetalDisplayLink(metalLayer: layer)
        link.delegate = self
        link.preferredFrameLatency = 1
        link.preferredFrameRateRange = Self.frameRateRange(governor.tier.refreshRate)
        link.add(to: .current, forMode: .default)
        displayLink = link
        while !stopRequested.get() {
            autoreleasepool {
                _ = RunLoop.current.run(mode: .default, before: Date(timeIntervalSinceNow: 0.05))
            }
        }
        link.invalidate()
        displayLink = nil
        let slips = slipBox.get()
        let airPodsLatency = airPods?.snapshot?.latency
        let summary = statistics.withLock { $0.summary(endedAt: Date(), slips: slips, airPodsLatency: airPodsLatency) }
        let result = VRSessionResult(summary: summary, profile: profileBox.get())
        // Strong: the sensors must stop even after the view controller is gone.
        DispatchQueue.main.async { self.finish(result) }
    }

    private static func frameRateRange(_ hz: Int) -> CAFrameRateRange {
        let rate = Float(hz)
        return CAFrameRateRange(minimum: rate, maximum: rate, preferred: rate)
    }

    func metalDisplayLink(_ link: CAMetalDisplayLink, needsUpdate update: CAMetalDisplayLink.Update) {
        autoreleasepool {
            renderFrame(link: link, update: update)
        }
    }

    private func renderFrame(link: CAMetalDisplayLink, update: CAMetalDisplayLink.Update) {
        let cpuStart = CACurrentMediaTime()
        let now = cpuStart
        let dt = lastFrameTime.map { min(max(now - $0, 0), 0.1) } ?? 0
        lastFrameTime = now
        let start = sessionStart ?? now
        sessionStart = start
        let time = now - start
        let worldTracking = worldTrackingBox.get()

        let tier = governor.tier
        let frameInterval = 1.0 / Double(tier.refreshRate)
        // Predict to the middle of scan-out, when the average pixel lights up.
        let displayTime = update.targetPresentationTimestamp + frameInterval * 0.5

        ingestSensors(now: now, worldTracking: worldTracking)
        experience.setPassthroughAvailable(worldTracking && tracking.cameraState == .running)

        var head = tracker.predictHead(at: displayTime)
        noteModeChange(head.mode, now: now)
        var sceneHead = playSpace.sceneFromWorld * head.worldFromScreen

        let controller = controllers.snapshot()
        handleInput(controller: controller, dt: dt, head: head, sceneHead: sceneHead, now: now)
        head = tracker.predictHead(at: displayTime)
        sceneHead = playSpace.sceneFromWorld * head.worldFromScreen
        lastHead = head

        updateGovernor(link: link, now: now)
        updateAirPods(now: now, worldTracking: worldTracking)
        updateSafety(head: head, dt: dt, worldTracking: worldTracking, controller: controller)

        let ray = selectionRay(sceneHead: sceneHead, controller: controller)
        let hit = experience.hit(origin: ray.origin, direction: ray.direction, head: sceneHead)

        let eyeSize = layout.eyeBufferSize(resolution: governor.tier.eyeResolution)
        guard let targets = try? renderer.ensureEyeTargets(width: eyeSize.width, height: eyeSize.height),
              let eyeCommands = renderer.commandQueue.makeCommandBuffer() else { return }
        eyeCommands.label = "eye pass"

        var cameraFrame: VRCameraTextureCache.Frame?
        let eyeFrame = buildEyeFrame(sceneHead: sceneHead, time: time, ray: ray, hit: hit, cameraFrame: &cameraFrame, worldTracking: worldTracking)
        renderer.encodeEyePass(eyeFrame, targets: targets, into: eyeCommands)
        let retainedCamera = cameraFrame
        eyeCommands.addCompletedHandler { [weak self] buffer in
            // Holding the camera textures here keeps them alive until the GPU is done.
            _ = retainedCamera
            let ms = (buffer.gpuEndTime - buffer.gpuStartTime) * 1000
            guard ms > 0, ms < 200 else { return }
            self?.gpuTimes.withLock { $0.eye.add(ms) }
            self?.statistics.withLock { $0.recordGPU(eyePassMilliseconds: ms, finalPassMilliseconds: nil) }
        }
        eyeCommands.commit()

        let estimates = gpuTimes.withLock { (eye: ($0.eye.value ?? 4) / 1000, final: ($0.final.value ?? 1) / 1000) }
        let wait = lateLatch.waitDuration(
            now: CACurrentMediaTime(),
            deadline: update.targetTimestamp,
            eyePassGPUTime: estimates.eye,
            finalPassGPUTime: estimates.final
        )
        VRClock.wait(seconds: wait)
        lastLatchWait = wait
        if let motion = tracking.pollMotion(), motion.timestamp > lastMotionTimestamp {
            lastMotionTimestamp = motion.timestamp
            tracker.ingest(motion)
            airPods?.addPhoneSample(motion)
        }
        let lateRotation = settings.timewarp ? tracker.predictRotation(at: displayTime) : head.worldFromScreen.rotation
        let timewarp = VRFrameBuilder.timewarpRotation(rendered: head.worldFromScreen.rotation, late: lateRotation)
        let brightness = Float(min(1, time / 0.4))
        let finalFrame = VRFinalFrame(
            eyes: VRFrameBuilder.distortionEyes(layout: layout, timewarp: timewarp, vignette: vignette),
            frame: VRFrameBuilder.distortionFrame(layout: layout, chromaticCorrection: settings.chromaticCorrection, brightness: brightness)
        )
        guard let finalCommands = renderer.commandQueue.makeCommandBuffer() else { return }
        finalCommands.label = "lens correction"
        let drawable = update.drawable
        renderer.encodeFinalPass(finalFrame, layout: layout, eyeTexture: targets.color, target: drawable.texture, into: finalCommands)
        let motionStamp = tracker.latestMotion?.timestamp
        let scheduledPresentation = update.targetPresentationTimestamp
        finalCommands.present(drawable)
        finalCommands.addCompletedHandler { [weak self] buffer in
            if let stamp = motionStamp {
                // A frame the GPU finishes after its slot shows at a later refresh.
                var presented = scheduledPresentation
                if buffer.gpuEndTime > presented {
                    presented += ((buffer.gpuEndTime - presented) / frameInterval).rounded(.up) * frameInterval
                }
                self?.statistics.withLock { $0.recordPhotonLatency(milliseconds: (presented - stamp) * 1000) }
            }
            let ms = (buffer.gpuEndTime - buffer.gpuStartTime) * 1000
            guard ms > 0, ms < 200 else { return }
            self?.gpuTimes.withLock { $0.final.add(ms) }
            self?.statistics.withLock { $0.recordGPU(eyePassMilliseconds: nil, finalPassMilliseconds: ms) }
        }
        finalCommands.commit()

        let cpuMilliseconds = (CACurrentMediaTime() - cpuStart - wait) * 1000
        let mode = head.mode
        let currentThermal = thermal
        let resolution = governor.tier.eyeResolution
        statistics.withLock {
            $0.recordFrame(
                presentationTime: update.targetPresentationTimestamp,
                expectedInterval: frameInterval,
                cpuMilliseconds: cpuMilliseconds,
                mode: mode,
                thermal: currentThermal,
                eyeResolution: resolution
            )
        }
        if settings.spatialAudio {
            audio.update(listener: sceneHead, beaconPosition: VRSceneLayout.beaconPosition(at: time))
        }
    }

    // MARK: - Sensors

    private func ingestSensors(now: TimeInterval, worldTracking: Bool) {
        if let motion = tracking.pollMotion(), motion.timestamp > lastMotionTimestamp {
            lastMotionTimestamp = motion.timestamp
            tracker.ingest(motion)
            airPods?.addPhoneSample(motion)
        }
        let latest = tracking.latest()
        if let sample = latest.tracking, sample.timestamp > lastTrackingTimestamp {
            lastTrackingTimestamp = sample.timestamp
            lastTrackingArrival = now
            tracker.ingest(sample)
        } else if worldTracking, tracker.mode == .sixDoF, let arrival = lastTrackingArrival, now - arrival > 0.5 {
            // ARKit went quiet (interrupted or failed): stop extrapolating its last position.
            tracker.ingest(VRTrackingSample(timestamp: now, worldFromCamera: matrix_identity_float4x4, quality: .unavailable))
        }
        if let floor = latest.floorHeight, !floorApplied {
            floorApplied = true
            playSpace.setFloorHeight(floor)
            show("Found the floor", now: now)
        }
    }

    private func noteModeChange(_ mode: VRTrackingMode, now: TimeInterval) {
        defer { lastMode = mode }
        guard let lastMode, lastMode != mode, !experience.isCountingDown else { return }
        show(mode == .sixDoF ? "Position tracking is back" : "Tracking limited: rotation only", now: now)
    }

    // MARK: - Input

    private func selectionRay(sceneHead: VRPose, controller: VRControllerSnapshot) -> (origin: SIMD3<Float>, direction: SIMD3<Float>, pointer: Bool) {
        guard let delta = controller.pointerDelta, !experience.isCountingDown else {
            return (sceneHead.position, sceneHead.rotation.act(SIMD3(0, 0, -1)), false)
        }
        // GameController reports rates like a phone lying flat: z out of the
        // face and y toward the far edge. That edge is the pointing direction.
        let controllerToPointer = VRMath.rotationX(-.pi / 2)
        let local = (controllerToPointer * delta * controllerToPointer.inverse).normalized
        let base = VRMath.rotationY(pointerHeading)
        let origin = sceneHead.position + base.act(SIMD3(0.16, -0.38, -0.22))
        return (origin, (base * local).act(SIMD3(0, 0, -1)), true)
    }

    private func handleInput(controller: VRControllerSnapshot, dt: TimeInterval, head: VRHeadPose, sceneHead: VRPose, now: TimeInterval) {
        let ray = selectionRay(sceneHead: sceneHead, controller: controller)
        let target = experience.hit(origin: ray.origin, direction: ray.direction, head: sceneHead)?.target
        var actions: [VRExperienceAction] = []

        let pending = commands.withLock { queued -> [VRSessionCommand] in
            let drained = queued
            queued.removeAll()
            return drained
        }
        for command in pending {
            switch command {
            case .tap: actions += experience.handle(.tap(target: target, head: sceneHead))
            case .longPress: actions += experience.handle(.longPress)
            }
        }

        for (button, count) in controller.presses where count > seenPresses[button, default: 0] {
            seenPresses[button] = count
            actions += experience.handle(.controller(button, target: target, head: sceneHead))
        }

        if !experience.isCountingDown {
            let turn = controller.rightStick.x
            if snapArmed, abs(turn) > 0.7 {
                snapArmed = false
                actions.append(.snapTurn(turn > 0 ? experience.snapTurnAngle : -experience.snapTurnAngle))
            } else if abs(turn) < 0.3 {
                snapArmed = true
            }
            var stick = controller.leftStick
            if simd_length(stick) < 0.15 { stick = .zero }
            if stick != .zero {
                playSpace.move(stick: stick, speed: settings.locomotionSpeed, dt: Float(dt), head: head.worldFromScreen)
            }
        }

        if let fired = dwell.update(target: target, dt: dt) {
            actions += experience.handle(.gazeSelected(fired, head: sceneHead))
        }
        actions += experience.handle(.tick(dt: dt, head: sceneHead))
        apply(actions, head: head, now: now)
    }

    private func apply(_ actions: [VRExperienceAction], head: VRHeadPose, now: TimeInterval) {
        for action in actions {
            switch action {
            case .recenter:
                playSpace.recenter(head: head.worldFromScreen)
                controllers.recenterPointer()
                pointerHeading = 0
                dwell.reset()
            case .exit:
                DispatchQueue.main.async { [weak self] in self?.onExitRequested?() }
            case .profileChanged:
                let profile = experience.state.profile
                layout = VRStereoLayout(screen: configuration.screen, profile: profile)
                profileBox.set(profile)
            case .sceneChanged:
                dwell.reset()
            case .passthroughChanged, .statsChanged:
                break
            case .snapTurn(let angle):
                playSpace.snapTurn(by: angle, head: head.worldFromScreen)
            case .haptic:
                controllers.playTap()
            }
        }
    }

    // MARK: - Policies

    private func updateGovernor(link: CAMetalDisplayLink, now: TimeInterval) {
        if now - lastPowerCheck > 0.5 {
            lastPowerCheck = now
            let state = ProcessInfo.processInfo.thermalState
            if state == .critical {
                thermal = .critical
            } else if state == .serious {
                thermal = .serious
            } else if state == .fair {
                thermal = .fair
            } else {
                thermal = .nominal
            }
            lowPower = ProcessInfo.processInfo.isLowPowerModeEnabled
        }
        let gpu = gpuTimes.withLock { g -> Double? in
            guard let eye = g.eye.value else { return nil }
            return (eye + (g.final.value ?? 0)) / 1000
        }
        let before = governor.tier
        guard governor.update(now: now, thermal: thermal, lowPower: lowPower, gpuFrameTime: gpu) else { return }
        let tier = governor.tier
        if tier.refreshRate != before.refreshRate {
            link.preferredFrameRateRange = Self.frameRateRange(tier.refreshRate)
            show(tier.refreshRate < before.refreshRate ? "Running warm: \(tier.refreshRate) Hz" : "\(tier.refreshRate) Hz", now: now)
        }
        if tier.reducedScene, !before.reducedScene {
            show("Very hot: simpler scene. Take a break soon.", now: now)
        }
    }

    private func updateAirPods(now: TimeInterval, worldTracking: Bool) {
        guard let airPods else { return }
        if let snapshot = airPods.snapshot {
            if snapshot.slipCount > lastSlips {
                lastSlips = snapshot.slipCount
                slipBox.set(lastSlips)
                show("The viewer moved. Look ahead and recenter.", now: now)
            }
            // With the camera off, nothing else checks yaw drift.
            if !worldTracking { tracker.yawBias = snapshot.yawBiasTarget }
        }
        airPods.setCurrentYawBias(tracker.yawBias)
    }

    /// Play-area wall, automatic passthrough outside it, and the comfort vignette.
    private func updateSafety(head: VRHeadPose, dt: TimeInterval, worldTracking: Bool, controller: VRControllerSnapshot) {
        let outside = worldTracking && head.mode == .sixDoF
            && playSpace.boundaryDistance(head: head.worldFromScreen.position) < -0.15
        let wantsCamera = experience.state.passthroughAvailable && (experience.state.passthrough || outside)
        let step = Float(dt) * 4
        passthroughOpacity = wantsCamera ? min(1, passthroughOpacity + step) : max(0, passthroughOpacity - step)
        tracking.setWantsCameraFrames(wantsCamera || passthroughOpacity > 0)

        let moving = settings.comfortVignette && simd_length(controller.leftStick) >= 0.15 && !experience.isCountingDown
        let target: Float = moving ? 0.72 : 1
        vignette += (target - vignette) * min(1, Float(dt) * 6)
    }

    private func show(_ text: String, now: TimeInterval) {
        message = (text, now + 3)
    }

    // MARK: - Frame building

    private func buildEyeFrame(
        sceneHead: VRPose,
        time: Double,
        ray: (origin: SIMD3<Float>, direction: SIMD3<Float>, pointer: Bool),
        hit: (target: VRGazeTarget, distance: Float)?,
        cameraFrame: inout VRCameraTextureCache.Frame?,
        worldTracking: Bool
    ) -> VREyeFrame {
        let state = experience.state
        let now = CACurrentMediaTime()
        let fullPassthrough = passthroughOpacity >= 0.99
        var instances = VRFrameBuilder.instances(
            scene: state.scene,
            reduced: governor.tier.reducedScene,
            time: time,
            passthrough: fullPassthrough
        )
        if !experience.isCountingDown, !state.menuOpen {
            instances.append(VRFrameBuilder.hubInstance(center: VRExperience.hubCenter(head: sceneHead), highlighted: hit?.target == .menuHub, time: time))
        }
        if ray.pointer {
            instances.append(VRFrameBuilder.pointerInstance(origin: ray.origin, direction: ray.direction, length: hit?.distance ?? 3))
        }

        let worldHead = lastHead?.worldFromScreen.position ?? .zero
        let distanceToEdge = playSpace.boundaryDistance(head: worldHead)
        let wallVisibility = worldTracking ? 1 - VRMath.smoothstep(0.2, 0.6, distanceToEdge) : 0
        let boundaryCenter = playSpace.boundaryCenterInScene

        var passthrough: VRPassthroughDraw?
        if passthroughOpacity > 0.01, let camera = tracking.latest().camera,
           let textures = cameraTextures.textures(for: camera.pixelBuffer) {
            cameraFrame = textures
            let sceneFromCamera = playSpace.sceneFromWorld * VRPose(camera.worldFromCamera)
            passthrough = VRPassthroughDraw(
                luma: textures.luma,
                chroma: textures.chroma,
                uniforms: VRFrameBuilder.passthroughUniforms(
                    sceneFromCamera: sceneFromCamera,
                    intrinsics: camera.intrinsics,
                    imageWidth: camera.imageWidth,
                    imageHeight: camera.imageHeight,
                    distance: 2.5,
                    opacity: passthroughOpacity
                )
            )
        }

        var panels: [VRDrawPanel] = []
        func add(_ slot: VRPanelPainter.Slot, _ content: VRPanelContent, at placement: VRPanelPlacement?) {
            guard let placement, let texture = painter.texture(for: slot, content: content) else { return }
            panels.append(VRDrawPanel(texture: texture, uniforms: VRFrameBuilder.panelUniforms(placement, opacity: 1)))
        }
        if case .countdown(let remaining) = state.phase {
            add(.countdown, .countdown(seconds: Int(remaining.rounded(.up)), subtitle: "Put the phone in the viewer"), at: state.countdownPlacement)
        }
        if state.scene == .calibration {
            var hovered: VRGazeTarget?
            if let target = hit?.target, case .calibrationStep = target { hovered = target }
            if hit?.target == .calibrationDone { hovered = .calibrationDone }
            let rows = VRCalibrationParameter.allCases.map { VRCalibrationRow(parameter: $0, value: $0.formatted(state.profile)) }
            add(.calibration, .calibration(VRCalibrationContent(rows: rows, selected: state.selectedParameter, hovered: hovered)), at: state.calibrationPlacement)
        }
        if state.menuOpen {
            var hovered: VRMenuItem?
            if let target = hit?.target, case .menu(let item) = target { hovered = item }
            let content = VRMenuContent(
                hovered: hovered,
                passthroughOn: state.passthrough,
                passthroughAvailable: state.passthroughAvailable,
                statsOn: state.showStats,
                scene: state.scene
            )
            add(.menu, .menu(content), at: state.menuPlacement)
        }
        if state.showStats {
            if now - lastStatsUpdate > 0.25 {
                lastStatsUpdate = now
                statsLines = makeStatsLines()
            }
            add(.stats, .stats(statsLines), at: VRFrameBuilder.headLocked(head: sceneHead, offset: SIMD3(-0.26, -0.3, -1.1), size: VRPanelLayouts.statsSize))
        }
        if let message, message.until > now {
            add(.message, .message(message.text), at: VRFrameBuilder.headLocked(head: sceneHead, offset: SIMD3(0, 0.24, -1.2), size: VRPanelLayouts.messageSize))
        }

        var reticle: VRPanelUniforms?
        if !experience.isCountingDown {
            let distance = hit?.distance ?? experience.panelDistance(origin: ray.origin, direction: ray.direction) ?? 2.5
            reticle = VRFrameBuilder.reticleUniforms(
                head: sceneHead,
                origin: ray.origin,
                direction: ray.direction,
                distance: distance,
                progress: dwell.progress,
                highlighted: hit != nil
            )
        }

        return VREyeFrame(
            eyes: VRFrameBuilder.eyeUniforms(layout: layout, sceneFromHead: sceneHead),
            frame: VRFrameBuilder.frameUniforms(boundaryCenter: boundaryCenter, boundaryRadius: playSpace.boundaryRadius, boundaryVisibility: wallVisibility),
            instances: instances,
            boundary: wallVisibility > 0.01 ? VRFrameBuilder.boundaryUniforms(center: boundaryCenter, radius: playSpace.boundaryRadius) : nil,
            panels: panels,
            reticle: reticle,
            passthrough: passthrough,
            drawSky: !fullPassthrough
        )
    }

    private func makeStatsLines() -> [String] {
        let s = statistics.withLock {
            (frame: $0.smoothedFrameInterval.value, cpu: $0.smoothedCPU.value, eye: $0.smoothedEyePass.value,
             final: $0.smoothedFinalPass.value, photon: $0.smoothedPhotonLatency.value)
        }
        let tier = governor.tier
        let size = layout.eyeBufferSize(resolution: tier.eyeResolution)
        let head = lastHead
        func ms(_ value: Double?) -> String { value.map { String(format: "%.1f", $0) } ?? "–" }
        var lines = [
            "\(tier.refreshRate) Hz · \(size.width)×\(size.height) per eye · \(renderer.usesAmplification ? "single pass" : "two passes")",
            "Frame \(ms(s.frame.map { $0 * 1000 })) ms · CPU \(ms(s.cpu)) ms",
            "GPU eyes \(ms(s.eye)) ms · lens \(ms(s.final)) ms",
            "Motion to photon \(ms(s.photon)) ms · latch \(ms(lastLatchWait * 1000)) ms",
        ]
        if let head {
            lines.append("\(head.mode == .sixDoF ? "6DoF" : "3DoF") · predict \(ms(head.rotationHorizon * 1000)) / \(ms(head.translationHorizon * 1000)) ms")
        }
        var last = "Thermal \(["nominal", "fair", "serious", "critical"][thermal.rawValue])"
        if let latency = airPods?.snapshot?.latency { last += " · AirPods \(ms(latency * 1000)) ms" }
        lines.append(last)
        return lines
    }
}
