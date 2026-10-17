import Foundation
import simd

/// Axis-aligned rectangle in panel texture coordinates (origin top left, v down).
struct VRRect: Equatable {
    var x: Float
    var y: Float
    var width: Float
    var height: Float

    func contains(_ p: SIMD2<Float>) -> Bool {
        p.x >= x && p.x <= x + width && p.y >= y && p.y <= y + height
    }

    var center: SIMD2<Float> { SIMD2(x + width / 2, y + height / 2) }
}

/// A flat panel in the scene. Its local +Z faces the viewer.
struct VRPanelPlacement {
    var center: SIMD3<Float>
    var rotation: simd_quatf
    /// Width and height, meters.
    var size: SIMD2<Float>

    var modelMatrix: simd_float4x4 {
        VRPose(rotation: rotation, position: center).matrix * VRMath.scale(SIMD3(size.x, size.y, 1))
    }

    /// Panel texture coordinates and distance where a ray hits the panel's front.
    func hit(origin: SIMD3<Float>, direction: SIMD3<Float>) -> (uv: SIMD2<Float>, distance: Float)? {
        let normal = rotation.act(SIMD3(0, 0, 1))
        guard simd_dot(direction, normal) < 0,
              let distance = VRMath.intersectPlane(rayOrigin: origin, direction: direction, planePoint: center, planeNormal: normal)
        else { return nil }
        let local = rotation.inverse.act(origin + direction * distance - center)
        let uv = SIMD2(local.x / size.x + 0.5, 0.5 - local.y / size.y)
        guard uv.x >= 0, uv.x <= 1, uv.y >= 0, uv.y <= 1 else { return nil }
        return (uv, distance)
    }

    /// A panel `distance` meters ahead of the head along its heading,
    /// `drop` meters below eye level, tilted back to face the eye.
    static func inFront(of head: VRPose, distance: Float, drop: Float, size: SIMD2<Float>) -> VRPanelPlacement {
        let heading = VRMath.heading(of: head.rotation)
        let forward = SIMD3(-sin(heading), 0, -cos(heading))
        let center = head.position + forward * distance - SIMD3(0, drop, 0)
        let tilt = -atan2(drop, distance)
        return VRPanelPlacement(center: center, rotation: (VRMath.rotationY(heading) * VRMath.rotationX(tilt)).normalized, size: size)
    }
}

enum VRMenuItem: String, CaseIterable, Identifiable {
    case recenter
    case passthrough
    case stats
    case close
    case exit

    var id: String { rawValue }
}

/// Viewer values the calibration scene adjusts while you look through the lenses.
enum VRCalibrationParameter: Int, CaseIterable, Identifiable {
    case k1
    case k2
    case redScale
    case blueScale
    case interLensDistance
    case screenToLensDistance

    var id: Int { rawValue }

    var title: String {
        switch self {
        case .k1: return "Distortion k1"
        case .k2: return "Distortion k2"
        case .redScale: return "Red scale"
        case .blueScale: return "Blue scale"
        case .interLensDistance: return "Lens spacing"
        case .screenToLensDistance: return "Screen to lens"
        }
    }

    var step: Float {
        switch self {
        case .k1, .k2: return 0.02
        case .redScale, .blueScale: return 0.001
        case .interLensDistance, .screenToLensDistance: return 0.0005
        }
    }

    func value(in profile: VRViewerProfile) -> Float {
        switch self {
        case .k1: return profile.distortionK1
        case .k2: return profile.distortionK2
        case .redScale: return profile.redScale
        case .blueScale: return profile.blueScale
        case .interLensDistance: return profile.interLensDistance
        case .screenToLensDistance: return profile.screenToLensDistance
        }
    }

    func adjusted(_ profile: VRViewerProfile, steps: Int) -> VRViewerProfile {
        var p = profile
        let value = self.value(in: profile) + Float(steps) * step
        switch self {
        case .k1: p.distortionK1 = value
        case .k2: p.distortionK2 = value
        case .redScale: p.redScale = value
        case .blueScale: p.blueScale = value
        case .interLensDistance: p.interLensDistance = value
        case .screenToLensDistance: p.screenToLensDistance = value
        }
        return p.clamped()
    }

    func formatted(_ profile: VRViewerProfile) -> String {
        let v = value(in: profile)
        switch self {
        case .k1, .k2: return String(format: "%.3f", v)
        case .redScale, .blueScale: return String(format: "%.4f", v)
        case .interLensDistance, .screenToLensDistance: return String(format: "%.1f mm", v * 1000)
        }
    }
}

/// Something the wearer can select by looking at it.
enum VRGazeTarget: Hashable {
    case menuHub
    case menu(VRMenuItem)
    case sceneSign(VRSceneKind)
    case calibrationStep(VRCalibrationParameter, Int)
    case calibrationDone
}

struct VRPanelButton: Equatable {
    var target: VRGazeTarget
    var frame: VRRect
}

/// Button rectangles shared by hit testing and the panel painter, so what you
/// see is what you select.
enum VRPanelLayouts {
    static let menuSize = SIMD2<Float>(0.70, 0.54)
    static let sceneSignSize = SIMD2<Float>(0.54, 0.48)
    static let calibrationSize = SIMD2<Float>(0.74, 0.58)
    static let statsSize = SIMD2<Float>(0.40, 0.22)
    static let countdownSize = SIMD2<Float>(0.60, 0.34)
    static let messageSize = SIMD2<Float>(0.62, 0.12)

    static let menuTitle = VRRect(x: 0.05, y: 0.03, width: 0.9, height: 0.12)
    static let sceneSignTitle = VRRect(x: 0.06, y: 0.04, width: 0.88, height: 0.14)

    /// One button per scene, stacked under the title. Order matches
    /// `VRSceneKind.allCases` so a new scene shows up on the sign.
    static let sceneSignButtons: [VRPanelButton] = {
        let scenes = VRSceneKind.allCases
        let top: Float = 0.22
        let gap: Float = 0.035
        let height: Float = (0.96 - top - gap * Float(scenes.count - 1)) / Float(scenes.count)
        return scenes.enumerated().map { index, scene in
            VRPanelButton(
                target: .sceneSign(scene),
                frame: VRRect(x: 0.06, y: top + Float(index) * (height + gap), width: 0.88, height: height)
            )
        }
    }()

    static let menuButtons: [VRPanelButton] = {
        let inset: Float = 0.05
        let gap: Float = 0.03
        let top: Float = 0.17
        let rows: Float = 4
        let rowHeight = (0.96 - top - gap * (rows - 1)) / rows
        func y(_ row: Int) -> Float { top + Float(row) * (rowHeight + gap) }
        func pair(_ row: Int, _ left: VRMenuItem, _ right: VRMenuItem) -> [VRPanelButton] {
            let width = (0.9 - gap) / 2
            return [
                VRPanelButton(target: .menu(left), frame: VRRect(x: inset, y: y(row), width: width, height: rowHeight)),
                VRPanelButton(target: .menu(right), frame: VRRect(x: inset + width + gap, y: y(row), width: width, height: rowHeight)),
            ]
        }
        var buttons: [VRPanelButton] = []
        buttons += pair(0, .recenter, .passthrough)
        buttons += pair(1, .stats, .close)
        let scenes = VRSceneKind.allCases
        let sceneWidth = (0.9 - gap * Float(scenes.count - 1)) / Float(scenes.count)
        for (index, scene) in scenes.enumerated() {
            buttons.append(VRPanelButton(
                target: .sceneSign(scene),
                frame: VRRect(x: inset + Float(index) * (sceneWidth + gap), y: y(2), width: sceneWidth, height: rowHeight)
            ))
        }
        buttons.append(VRPanelButton(
            target: .menu(.exit),
            frame: VRRect(x: inset, y: y(3), width: 0.9, height: rowHeight)
        ))
        return buttons
    }()

    static let calibrationTitle = VRRect(x: 0.04, y: 0.02, width: 0.92, height: 0.1)

    static func calibrationRow(_ parameter: VRCalibrationParameter) -> VRRect {
        let top: Float = 0.14
        let rowHeight: Float = 0.68 / Float(VRCalibrationParameter.allCases.count)
        return VRRect(x: 0.04, y: top + Float(parameter.rawValue) * rowHeight, width: 0.92, height: rowHeight - 0.012)
    }

    static let calibrationButtons: [VRPanelButton] = {
        var buttons: [VRPanelButton] = []
        for parameter in VRCalibrationParameter.allCases {
            let row = calibrationRow(parameter)
            buttons.append(VRPanelButton(target: .calibrationStep(parameter, -1), frame: VRRect(x: 0.47, y: row.y, width: 0.12, height: row.height)))
            buttons.append(VRPanelButton(target: .calibrationStep(parameter, 1), frame: VRRect(x: 0.84, y: row.y, width: 0.12, height: row.height)))
        }
        buttons.append(VRPanelButton(target: .calibrationDone, frame: VRRect(x: 0.3, y: 0.85, width: 0.4, height: 0.12)))
        return buttons
    }()

    static func button(at uv: SIMD2<Float>, in buttons: [VRPanelButton]) -> VRGazeTarget? {
        buttons.first { $0.frame.contains(uv) }?.target
    }
}

enum VRControllerButton: Equatable {
    case a
    case b
    case x
    case y
    case menu
    case options
    case dpadUp
    case dpadDown
    case dpadLeft
    case dpadRight
    case leftShoulder
    case rightShoulder
}

struct VRExperienceState {
    enum Phase: Equatable {
        case countdown(remaining: Double)
        case running
    }

    var phase: Phase
    var scene: VRSceneKind = .studio
    var menuOpen = false
    var passthrough = false
    var passthroughAvailable: Bool
    var showStats: Bool
    var profile: VRViewerProfile
    var selectedParameter: VRCalibrationParameter = .k1
    var menuPlacement: VRPanelPlacement?
    var calibrationPlacement: VRPanelPlacement?
    var countdownPlacement: VRPanelPlacement?
}

enum VRExperienceEvent {
    /// Time passes; `head` is the head pose in scene coordinates.
    case tick(dt: Double, head: VRPose)
    /// The screen was tapped (a viewer lever or a finger).
    case tap(target: VRGazeTarget?, head: VRPose)
    case longPress
    case controller(VRControllerButton, target: VRGazeTarget?, head: VRPose)
    case gazeSelected(VRGazeTarget, head: VRPose)
}

enum VRExperienceAction: Equatable {
    case recenter
    case exit
    case profileChanged
    case sceneChanged(VRSceneKind)
    case passthroughChanged(Bool)
    case statsChanged(Bool)
    /// Radians; positive turns right.
    case snapTurn(Float)
    case haptic
}

/// The in-headset interaction model: countdown, menu, calibration, and toggles.
///
/// Everything is reachable without touching the screen. Look at the standing
/// sign in the studio to pick a scene. Look down at the ring by your feet
/// (or tap, or press Menu) to open the menu, and select by holding your
/// gaze on a button, tapping, or pressing A.
struct VRExperience {
    private(set) var state: VRExperienceState
    var snapTurnAngle: Float = VRMath.radians(30)
    static let hubRadius: Float = 0.24

    init(profile: VRViewerProfile, countdown: Double, passthroughAvailable: Bool, showStats: Bool) {
        state = VRExperienceState(
            phase: countdown > 0 ? .countdown(remaining: countdown) : .running,
            passthroughAvailable: passthroughAvailable,
            showStats: showStats,
            profile: profile
        )
    }

    var isCountingDown: Bool {
        if case .countdown = state.phase { return true }
        return false
    }

    mutating func setPassthroughAvailable(_ available: Bool) {
        state.passthroughAvailable = available
        if !available { state.passthrough = false }
    }

    mutating func setProfile(_ profile: VRViewerProfile) {
        state.profile = profile.clamped()
    }

    /// The menu hub: a ring on the floor just ahead of the feet.
    static func hubCenter(head: VRPose) -> SIMD3<Float> {
        let heading = VRMath.heading(of: head.rotation)
        let forward = SIMD3(-sin(heading), 0, -cos(heading))
        return SIMD3(head.position.x, 0.005, head.position.z) + forward * 0.3
    }

    /// What the head's forward ray points at.
    func gazeTarget(head: VRPose) -> VRGazeTarget? {
        hit(origin: head.position, direction: head.rotation.act(SIMD3(0, 0, -1)), head: head)?.target
    }

    /// The nearest selectable thing along a ray (the gaze or a controller
    /// pointer), with its distance. `head` places the floor hub.
    func hit(origin: SIMD3<Float>, direction rawDirection: SIMD3<Float>, head: VRPose) -> (target: VRGazeTarget, distance: Float)? {
        guard !isCountingDown, simd_length(rawDirection) > 0 else { return nil }
        let direction = simd_normalize(rawDirection)
        var best: (target: VRGazeTarget, distance: Float)?
        func consider(_ placement: VRPanelPlacement?, _ buttons: [VRPanelButton]) {
            guard let placement, let hit = placement.hit(origin: origin, direction: direction) else { return }
            guard let target = VRPanelLayouts.button(at: hit.uv, in: buttons) else { return }
            if best == nil || hit.distance < (best?.distance ?? .infinity) { best = (target, hit.distance) }
        }
        if state.menuOpen { consider(state.menuPlacement, VRPanelLayouts.menuButtons) }
        if state.scene == .studio { consider(VRSceneLayout.sceneSignPlacement, VRPanelLayouts.sceneSignButtons) }
        if state.scene == .calibration { consider(state.calibrationPlacement, VRPanelLayouts.calibrationButtons) }
        if let best { return best }
        if !state.menuOpen, direction.y < -0.5,
           let distance = VRMath.intersectPlane(rayOrigin: origin, direction: direction, planePoint: .zero, planeNormal: SIMD3(0, 1, 0)) {
            let point = origin + direction * distance
            let center = Self.hubCenter(head: head)
            if simd_length(SIMD2(point.x - center.x, point.z - center.z)) <= Self.hubRadius { return (.menuHub, distance) }
        }
        return nil
    }

    /// Distance to whatever opaque panel the ray crosses, for placing the
    /// reticle on the panel even between buttons.
    func panelDistance(origin: SIMD3<Float>, direction: SIMD3<Float>) -> Float? {
        guard simd_length(direction) > 0 else { return nil }
        let unit = simd_normalize(direction)
        var placements: [VRPanelPlacement] = []
        if state.menuOpen, let menu = state.menuPlacement { placements.append(menu) }
        if state.scene == .studio { placements.append(VRSceneLayout.sceneSignPlacement) }
        if state.scene == .calibration, let panel = state.calibrationPlacement { placements.append(panel) }
        return placements.compactMap { $0.hit(origin: origin, direction: unit)?.distance }.min()
    }

    mutating func handle(_ event: VRExperienceEvent) -> [VRExperienceAction] {
        switch event {
        case .tick(let dt, let head):
            return tick(dt: dt, head: head)
        case .tap(let target, let head):
            if isCountingDown { return finishCountdown() }
            if let target { return activate(target, head: head) }
            return toggleMenu(head: head)
        case .longPress:
            return isCountingDown ? finishCountdown() : [.recenter]
        case .controller(let button, let target, let head):
            if isCountingDown { return finishCountdown() }
            return press(button, target: target, head: head)
        case .gazeSelected(let target, let head):
            guard !isCountingDown else { return [] }
            return activate(target, head: head)
        }
    }

    // MARK: - Private

    private mutating func tick(dt: Double, head: VRPose) -> [VRExperienceAction] {
        guard case .countdown(let remaining) = state.phase else { return [] }
        if let placement = state.countdownPlacement {
            let offAxis = abs(VRMath.wrapAngle(VRMath.heading(of: head.rotation) - VRMath.heading(of: placement.rotation)))
            if offAxis > VRMath.radians(50) { state.countdownPlacement = nil }
        }
        if state.countdownPlacement == nil {
            state.countdownPlacement = .inFront(of: head, distance: 1.4, drop: 0.05, size: VRPanelLayouts.countdownSize)
        }
        let next = remaining - dt
        if next <= 0 { return finishCountdown() }
        state.phase = .countdown(remaining: next)
        return []
    }

    private mutating func finishCountdown() -> [VRExperienceAction] {
        state.phase = .running
        state.countdownPlacement = nil
        return [.recenter, .haptic]
    }

    private mutating func toggleMenu(head: VRPose) -> [VRExperienceAction] {
        if state.menuOpen {
            state.menuOpen = false
            state.menuPlacement = nil
        } else {
            state.menuOpen = true
            state.menuPlacement = .inFront(of: head, distance: 0.95, drop: 0.12, size: VRPanelLayouts.menuSize)
        }
        return [.haptic]
    }

    private mutating func setScene(_ scene: VRSceneKind, head: VRPose) -> [VRExperienceAction] {
        if scene == state.scene { return [] }
        state.scene = scene
        state.menuOpen = false
        state.menuPlacement = nil
        // Low enough that its top edge sits below the eye line, leaving the
        // view straight ahead for the target and the focus chart.
        state.calibrationPlacement = scene == .calibration
            ? .inFront(of: head, distance: 1.15, drop: 0.4, size: VRPanelLayouts.calibrationSize)
            : nil
        return [.sceneChanged(scene), .haptic]
    }

    private mutating func adjust(_ parameter: VRCalibrationParameter, steps: Int) -> [VRExperienceAction] {
        state.selectedParameter = parameter
        let next = parameter.adjusted(state.profile, steps: steps)
        guard next != state.profile else { return [] }
        state.profile = next
        return [.profileChanged]
    }

    private mutating func activate(_ target: VRGazeTarget, head: VRPose) -> [VRExperienceAction] {
        switch target {
        case .menuHub:
            return state.menuOpen ? [] : toggleMenu(head: head)
        case .menu(let item):
            switch item {
            case .recenter:
                state.menuOpen = false
                state.menuPlacement = nil
                return [.recenter, .haptic]
            case .passthrough:
                guard state.passthroughAvailable else { return [] }
                state.passthrough.toggle()
                return [.passthroughChanged(state.passthrough), .haptic]
            case .stats:
                state.showStats.toggle()
                return [.statsChanged(state.showStats), .haptic]
            case .close:
                state.menuOpen = false
                state.menuPlacement = nil
                return [.haptic]
            case .exit:
                return [.exit]
            }
        case .sceneSign(let scene):
            return setScene(scene, head: head)
        case .calibrationStep(let parameter, let direction):
            return adjust(parameter, steps: direction)
        case .calibrationDone:
            return setScene(.studio, head: head)
        }
    }

    private mutating func press(_ button: VRControllerButton, target: VRGazeTarget?, head: VRPose) -> [VRExperienceAction] {
        let calibrating = state.scene == .calibration
        switch button {
        case .a:
            if let target { return activate(target, head: head) }
            return toggleMenu(head: head)
        case .b:
            if state.menuOpen { return toggleMenu(head: head) }
            if calibrating || state.scene == .minecraft { return setScene(.studio, head: head) }
            return []
        case .x:
            return activate(.menu(.passthrough), head: head)
        case .y:
            return activate(.menu(.stats), head: head)
        case .menu:
            return toggleMenu(head: head)
        case .options:
            return [.recenter, .haptic]
        case .dpadUp, .dpadDown:
            guard calibrating else { return [] }
            let all = VRCalibrationParameter.allCases
            let delta = button == .dpadUp ? -1 : 1
            let index = (state.selectedParameter.rawValue + delta + all.count) % all.count
            state.selectedParameter = all[index]
            return []
        case .dpadLeft, .dpadRight:
            let direction = button == .dpadRight ? 1 : -1
            if calibrating { return adjust(state.selectedParameter, steps: direction) }
            return [.snapTurn(Float(direction) * snapTurnAngle)]
        case .leftShoulder:
            return [.snapTurn(-snapTurnAngle)]
        case .rightShoulder:
            return [.snapTurn(snapTurnAngle)]
        }
    }
}
