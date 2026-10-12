import Foundation
import simd

/// A rigid transform that rotates and then translates: `x' = rotation * x + position`.
///
/// Names in this experiment follow `aFromB`: a pose named `worldFromScreen`
/// maps points in the screen frame into the world frame.
struct VRPose {
    var rotation: simd_quatf
    var position: SIMD3<Float>

    static let identity = VRPose(rotation: VRMath.identityRotation, position: .zero)

    init(rotation: simd_quatf, position: SIMD3<Float>) {
        self.rotation = rotation
        self.position = position
    }

    init(_ matrix: simd_float4x4) {
        rotation = simd_quatf(matrix).normalized
        position = SIMD3(matrix.columns.3.x, matrix.columns.3.y, matrix.columns.3.z)
    }

    var matrix: simd_float4x4 {
        var m = simd_float4x4(rotation)
        m.columns.3 = SIMD4(position, 1)
        return m
    }

    var inverse: VRPose {
        let inverseRotation = rotation.inverse
        return VRPose(rotation: inverseRotation, position: -inverseRotation.act(position))
    }

    func transformPoint(_ point: SIMD3<Float>) -> SIMD3<Float> {
        rotation.act(point) + position
    }

    func transformDirection(_ direction: SIMD3<Float>) -> SIMD3<Float> {
        rotation.act(direction)
    }

    /// Composition: `(a * b).transformPoint(x) == a.transformPoint(b.transformPoint(x))`.
    static func * (a: VRPose, b: VRPose) -> VRPose {
        VRPose(rotation: (a.rotation * b.rotation).normalized, position: a.rotation.act(b.position) + a.position)
    }
}

/// Signed tangents of a frustum's half-angles. `left` and `bottom` are
/// negative for a frustum that contains its optical axis.
struct VRTangents: Equatable, Codable {
    var left: Float
    var right: Float
    var bottom: Float
    var top: Float

    var width: Float { right - left }
    var height: Float { top - bottom }

    /// Normalized device coordinates (y up) for a tangent-space direction.
    func ndc(fromTangent t: SIMD2<Float>) -> SIMD2<Float> {
        SIMD2((2 * t.x - (right + left)) / width, (2 * t.y - (top + bottom)) / height)
    }

    /// Texture coordinates (origin at the top left, v down) for a tangent-space direction.
    func uv(fromTangent t: SIMD2<Float>) -> SIMD2<Float> {
        SIMD2((t.x - left) / width, (top - t.y) / height)
    }

    func tangent(fromUV uv: SIMD2<Float>) -> SIMD2<Float> {
        SIMD2(left + uv.x * width, top - uv.y * height)
    }

    /// Widens every side by `degrees` of visual angle.
    func expanded(byDegrees degrees: Float) -> VRTangents {
        let margin = degrees * .pi / 180
        func widen(_ t: Float) -> Float {
            let angle = atan(abs(t)) + margin
            let clamped = min(angle, 85 * .pi / 180)
            return t < 0 ? -tan(clamped) : tan(clamped)
        }
        return VRTangents(left: widen(left), right: widen(right), bottom: widen(bottom), top: widen(top))
    }

    func contains(_ t: SIMD2<Float>) -> Bool {
        t.x >= left && t.x <= right && t.y >= bottom && t.y <= top
    }
}

enum VRMath {
    static let identityRotation = simd_quatf(ix: 0, iy: 0, iz: 0, r: 1)
    static let up = SIMD3<Float>(0, 1, 0)

    static func degrees(_ radians: Float) -> Float { radians * 180 / .pi }
    static func radians(_ degrees: Float) -> Float { degrees * .pi / 180 }

    static func rotationX(_ angle: Float) -> simd_quatf { simd_quatf(angle: angle, axis: SIMD3(1, 0, 0)) }
    static func rotationY(_ angle: Float) -> simd_quatf { simd_quatf(angle: angle, axis: SIMD3(0, 1, 0)) }
    static func rotationZ(_ angle: Float) -> simd_quatf { simd_quatf(angle: angle, axis: SIMD3(0, 0, 1)) }

    /// Wraps an angle into `(-π, π]`.
    static func wrapAngle(_ angle: Float) -> Float {
        var a = angle.truncatingRemainder(dividingBy: 2 * .pi)
        if a <= -.pi { a += 2 * .pi }
        if a > .pi { a -= 2 * .pi }
        return a
    }

    static func wrapAngle(_ angle: Double) -> Double {
        var a = angle.truncatingRemainder(dividingBy: 2 * .pi)
        if a <= -.pi { a += 2 * .pi }
        if a > .pi { a -= 2 * .pi }
        return a
    }

    /// Unit quaternion for a rotation vector (axis times angle in radians).
    static func rotation(fromVector rotationVector: SIMD3<Float>) -> simd_quatf {
        let angle = simd_length(rotationVector)
        if angle < 1e-6 {
            return simd_quatf(real: 1 - angle * angle / 8, imag: rotationVector * 0.5).normalized
        }
        return simd_quatf(angle: angle, axis: rotationVector / angle)
    }

    /// Rotation vector of the shortest rotation equivalent to `q`.
    static func rotationVector(of q: simd_quatf) -> SIMD3<Float> {
        var v = q.vector
        let length = simd_length(v)
        guard length > 1e-12 else { return .zero }
        v /= length
        if v.w < 0 { v = -v }
        let imaginary = SIMD3(v.x, v.y, v.z)
        let s = simd_length(imaginary)
        if s < 1e-7 { return imaginary * 2 }
        return imaginary / s * (2 * atan2(s, v.w))
    }

    /// Advances an attitude by a body-frame angular velocity held constant for `dt` seconds.
    static func integrate(_ attitude: simd_quatf, bodyRate: SIMD3<Float>, dt: Float) -> simd_quatf {
        (attitude * rotation(fromVector: bodyRate * dt)).normalized
    }

    /// Smallest angle, in radians, between two orientations.
    static func angleBetween(_ a: simd_quatf, _ b: simd_quatf) -> Float {
        let d = abs(simd_dot(a.normalized.vector, b.normalized.vector))
        return 2 * acos(min(1, d))
    }

    /// The part of `q` that rotates about `axis` (swing-twist decomposition).
    static func twist(of q: simd_quatf, about axis: SIMD3<Float>) -> simd_quatf {
        let unitAxis = simd_normalize(axis)
        let projection = simd_dot(q.imag, unitAxis) * unitAxis
        let candidate = simd_quatf(real: q.real, imag: projection)
        let length = candidate.length
        guard length > 1e-6 else { return identityRotation }
        return simd_quatf(vector: candidate.vector / length)
    }

    /// Angle about +Y of the vertical twist of `q`, wrapped to `(-π, π]`.
    static func yawAboutUp(of q: simd_quatf) -> Float {
        let t = twist(of: q, about: up)
        return wrapAngle(2 * atan2(t.imag.y, t.real))
    }

    /// Heading of a head pose whose -Z axis looks forward: the rotation about +Y
    /// that turns the world's -Z toward where the head faces. Looking straight
    /// up or down falls back to the head's up vector, so recentering never
    /// picks a random heading.
    static func heading(of rotation: simd_quatf) -> Float {
        let forward = rotation.act(SIMD3(0, 0, -1))
        var planar = SIMD2(forward.x, forward.z)
        if simd_length(planar) < 0.2 {
            let headUp = rotation.act(SIMD3(0, 1, 0))
            let sign: Float = forward.y < 0 ? 1 : -1
            planar = SIMD2(headUp.x, headUp.z) * sign
        }
        guard simd_length(planar) > 1e-6 else { return 0 }
        return atan2(-planar.x, -planar.y)
    }

    /// Reversed-Z, infinite-far perspective projection for a right-handed view
    /// space that looks down -Z. Depth is 1 at `near` and approaches 0 at infinity.
    static func perspective(_ tangents: VRTangents, near: Float) -> simd_float4x4 {
        let w = tangents.width
        let h = tangents.height
        return simd_float4x4(
            SIMD4(2 / w, 0, 0, 0),
            SIMD4(0, 2 / h, 0, 0),
            SIMD4((tangents.right + tangents.left) / w, (tangents.top + tangents.bottom) / h, 0, -1),
            SIMD4(0, 0, near, 0)
        )
    }

    static func translation(_ t: SIMD3<Float>) -> simd_float4x4 {
        var m = matrix_identity_float4x4
        m.columns.3 = SIMD4(t, 1)
        return m
    }

    static func scale(_ s: SIMD3<Float>) -> simd_float4x4 {
        simd_float4x4(diagonal: SIMD4(s, 1))
    }

    static func rotationMatrix3(_ q: simd_quatf) -> simd_float3x3 {
        simd_float3x3(q)
    }

    /// Ray-plane intersection. Returns the distance along `direction`, or nil
    /// when the ray is parallel to the plane or the plane is behind the origin.
    static func intersectPlane(
        rayOrigin: SIMD3<Float>,
        direction: SIMD3<Float>,
        planePoint: SIMD3<Float>,
        planeNormal: SIMD3<Float>
    ) -> Float? {
        let denominator = simd_dot(direction, planeNormal)
        guard abs(denominator) > 1e-6 else { return nil }
        let t = simd_dot(planePoint - rayOrigin, planeNormal) / denominator
        return t >= 0 ? t : nil
    }

    static func smoothstep(_ edge0: Float, _ edge1: Float, _ x: Float) -> Float {
        let t = min(max((x - edge0) / (edge1 - edge0), 0), 1)
        return t * t * (3 - 2 * t)
    }

    /// Fraction to blend toward a target each step so a first-order filter has
    /// time constant `tau`.
    static func blendFactor(dt: Double, tau: Double) -> Float {
        guard tau > 0 else { return 1 }
        guard dt > 0 else { return 0 }
        return Float(1 - exp(-dt / tau))
    }
}

/// Fixed-capacity FIFO that overwrites its oldest element.
struct VRRingBuffer<Element> {
    private var storage: [Element] = []
    private var head = 0
    let capacity: Int

    init(capacity: Int) {
        precondition(capacity > 0)
        self.capacity = capacity
        storage.reserveCapacity(capacity)
    }

    var count: Int { storage.count }
    var isEmpty: Bool { storage.isEmpty }

    mutating func append(_ element: Element) {
        if storage.count < capacity {
            storage.append(element)
        } else {
            storage[head] = element
            head = (head + 1) % capacity
        }
    }

    mutating func removeAll() {
        storage.removeAll(keepingCapacity: true)
        head = 0
    }

    /// Element `index` in insertion order (0 is the oldest).
    subscript(index: Int) -> Element {
        storage[(head + index) % storage.count]
    }

    var last: Element? {
        guard !storage.isEmpty else { return nil }
        return self[storage.count - 1]
    }

    var first: Element? {
        guard !storage.isEmpty else { return nil }
        return self[0]
    }

    var elements: [Element] {
        (0..<storage.count).map { self[$0] }
    }
}
