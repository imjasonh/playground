import Foundation
import simd

/// Vertex layout shared with the scene shaders: position, normal, and an
/// sRGB color packed RGBA8 with red in the low byte. 28 bytes, no padding.
struct VRSceneVertex: Equatable {
    var px: Float
    var py: Float
    var pz: Float
    var nx: Float
    var ny: Float
    var nz: Float
    var color: UInt32

    init(position: SIMD3<Float>, normal: SIMD3<Float>, color: UInt32) {
        px = position.x
        py = position.y
        pz = position.z
        nx = normal.x
        ny = normal.y
        nz = normal.z
        self.color = color
    }

    var position: SIMD3<Float> { SIMD3(px, py, pz) }
    var normal: SIMD3<Float> { SIMD3(nx, ny, nz) }
}

struct VRMesh {
    var vertices: [VRSceneVertex] = []
    var indices: [UInt16] = []

    /// Appends a triangle wound counterclockwise as seen from the side its
    /// vertex normals face, whatever order the corners arrive in.
    mutating func addTriangle(_ a: VRSceneVertex, _ b: VRSceneVertex, _ c: VRSceneVertex) {
        let base = UInt16(vertices.count)
        let geometric = simd_cross(b.position - a.position, c.position - a.position)
        let facing = a.normal + b.normal + c.normal
        vertices.append(a)
        if simd_dot(geometric, facing) >= 0 {
            vertices.append(b)
            vertices.append(c)
        } else {
            vertices.append(c)
            vertices.append(b)
        }
        indices.append(contentsOf: [base, base + 1, base + 2])
    }

    mutating func addQuad(_ a: VRSceneVertex, _ b: VRSceneVertex, _ c: VRSceneVertex, _ d: VRSceneVertex) {
        addTriangle(a, b, c)
        addTriangle(a, c, d)
    }
}

/// sRGB hex colors packed for `VRSceneVertex.color`.
enum VRPalette {
    static func rgba(_ hex: UInt32, alpha: UInt8 = 255) -> UInt32 {
        let r = (hex >> 16) & 0xFF
        let g = (hex >> 8) & 0xFF
        let b = hex & 0xFF
        return r | (g << 8) | (b << 16) | (UInt32(alpha) << 24)
    }

    /// Encodes linear RGB in `0...1` to the packed sRGB the scene vertex
    /// shader decodes. Voxel meshes store linear face colors, so they go
    /// through this before upload.
    static func packLinear(_ rgb: SIMD3<Float>, alpha: UInt8 = 255) -> UInt32 {
        func encode(_ c: Float) -> UInt32 {
            let x = max(0, min(1, c))
            let srgb = x <= 0.0031308 ? 12.92 * x : 1.055 * pow(x, 1 / 2.4) - 0.055
            return UInt32((srgb * 255).rounded())
        }
        return encode(rgb.x) | encode(rgb.y) << 8 | encode(rgb.z) << 16 | UInt32(alpha) << 24
    }

    /// A packed color as linear RGB with straight alpha, for shader tints.
    static func linear(_ packed: UInt32) -> SIMD4<Float> {
        func channel(_ shift: UInt32) -> Float { Float((packed >> shift) & 0xFF) / 255 }
        func decode(_ c: Float) -> Float { c <= 0.04045 ? c / 12.92 : pow((c + 0.055) / 1.055, 2.4) }
        return SIMD4(decode(channel(0)), decode(channel(8)), decode(channel(16)), channel(24))
    }

    static let floor = rgba(0x1F252D)
    static let plinth = rgba(0xE2E8F0)
    static let coral = rgba(0xF56565)
    static let amber = rgba(0xECC94B)
    static let sky = rgba(0x63B3ED)
    static let violet = rgba(0x9F7AEA)
    static let stone = rgba(0xCBD5E0)
    static let slate = rgba(0x2D3748)
    static let rose = rgba(0xF687B3)
    static let beacon = rgba(0xFBD38D)
    static let white = rgba(0xFFFFFF)
    static let teal = rgba(0x4FD1C5)
}

enum VRMeshKind: Int, CaseIterable {
    case cube
    case icosahedron
    case sphere
    case cylinder
    case torus
    case floor
    case room
    case boundary
    case disc
}

/// Procedural geometry, all unit-sized so the scene scales it per object.
enum VRMeshFactory {
    static func mesh(_ kind: VRMeshKind) -> VRMesh {
        switch kind {
        case .cube: return box(color: VRPalette.white)
        case .icosahedron: return icosphere(subdivisions: 0, flat: true, color: VRPalette.white)
        case .sphere: return icosphere(subdivisions: 2, flat: false, color: VRPalette.white)
        case .cylinder: return cylinder(segments: 24, color: VRPalette.white)
        case .torus: return torus(majorRadius: 1, minorRadius: 0.12, segments: 48, sides: 12, color: VRPalette.white)
        case .floor: return floor(halfExtent: 30)
        case .room: return room()
        case .boundary: return openCylinder(segments: 64)
        case .disc: return disc(segments: 48, color: VRPalette.white)
        }
    }

    /// Unit cube centred on the origin, flat shaded.
    static func box(color: UInt32) -> VRMesh {
        var mesh = VRMesh()
        let faces: [(n: SIMD3<Float>, u: SIMD3<Float>, v: SIMD3<Float>)] = [
            (SIMD3(1, 0, 0), SIMD3(0, 0, -1), SIMD3(0, 1, 0)),
            (SIMD3(-1, 0, 0), SIMD3(0, 0, 1), SIMD3(0, 1, 0)),
            (SIMD3(0, 1, 0), SIMD3(1, 0, 0), SIMD3(0, 0, -1)),
            (SIMD3(0, -1, 0), SIMD3(1, 0, 0), SIMD3(0, 0, 1)),
            (SIMD3(0, 0, 1), SIMD3(1, 0, 0), SIMD3(0, 1, 0)),
            (SIMD3(0, 0, -1), SIMD3(-1, 0, 0), SIMD3(0, 1, 0)),
        ]
        for face in faces {
            let c = face.n * 0.5
            let corners = [c - face.u * 0.5 - face.v * 0.5, c + face.u * 0.5 - face.v * 0.5,
                           c + face.u * 0.5 + face.v * 0.5, c - face.u * 0.5 + face.v * 0.5]
            let v = corners.map { VRSceneVertex(position: $0, normal: face.n, color: color) }
            mesh.addQuad(v[0], v[1], v[2], v[3])
        }
        return mesh
    }

    /// Unit-radius icosphere. `flat` gives each facet its own normal.
    static func icosphere(subdivisions: Int, flat: Bool, color: UInt32) -> VRMesh {
        let t: Float = (1 + Float(5).squareRoot()) / 2
        var points: [SIMD3<Float>] = [
            SIMD3(-1, t, 0), SIMD3(1, t, 0), SIMD3(-1, -t, 0), SIMD3(1, -t, 0),
            SIMD3(0, -1, t), SIMD3(0, 1, t), SIMD3(0, -1, -t), SIMD3(0, 1, -t),
            SIMD3(t, 0, -1), SIMD3(t, 0, 1), SIMD3(-t, 0, -1), SIMD3(-t, 0, 1),
        ].map { simd_normalize($0) }
        var faces: [(Int, Int, Int)] = [
            (0, 11, 5), (0, 5, 1), (0, 1, 7), (0, 7, 10), (0, 10, 11),
            (1, 5, 9), (5, 11, 4), (11, 10, 2), (10, 7, 6), (7, 1, 8),
            (3, 9, 4), (3, 4, 2), (3, 2, 6), (3, 6, 8), (3, 8, 9),
            (4, 9, 5), (2, 4, 11), (6, 2, 10), (8, 6, 7), (9, 8, 1),
        ]
        for _ in 0..<subdivisions {
            var midpoints: [Int: Int] = [:]
            func midpoint(_ a: Int, _ b: Int) -> Int {
                let key = min(a, b) * 1_000_003 + max(a, b)
                if let existing = midpoints[key] { return existing }
                points.append(simd_normalize((points[a] + points[b]) / 2))
                midpoints[key] = points.count - 1
                return points.count - 1
            }
            var next: [(Int, Int, Int)] = []
            for (a, b, c) in faces {
                let ab = midpoint(a, b)
                let bc = midpoint(b, c)
                let ca = midpoint(c, a)
                next.append(contentsOf: [(a, ab, ca), (b, bc, ab), (c, ca, bc), (ab, bc, ca)])
            }
            faces = next
        }
        var mesh = VRMesh()
        for (a, b, c) in faces {
            let pa = points[a], pb = points[b], pc = points[c]
            if flat {
                let n = simd_normalize(pa + pb + pc)
                mesh.addTriangle(
                    VRSceneVertex(position: pa, normal: n, color: color),
                    VRSceneVertex(position: pb, normal: n, color: color),
                    VRSceneVertex(position: pc, normal: n, color: color)
                )
            } else {
                mesh.addTriangle(
                    VRSceneVertex(position: pa, normal: pa, color: color),
                    VRSceneVertex(position: pb, normal: pb, color: color),
                    VRSceneVertex(position: pc, normal: pc, color: color)
                )
            }
        }
        return mesh
    }

    /// Unit-radius cylinder from y = 0 to y = 1 with caps.
    static func cylinder(segments: Int, color: UInt32) -> VRMesh {
        var mesh = VRMesh()
        let up = SIMD3<Float>(0, 1, 0)
        for i in 0..<segments {
            let a0 = Float(i) / Float(segments) * 2 * .pi
            let a1 = Float(i + 1) / Float(segments) * 2 * .pi
            let d0 = SIMD3(cos(a0), 0, sin(a0))
            let d1 = SIMD3(cos(a1), 0, sin(a1))
            mesh.addQuad(
                VRSceneVertex(position: d0, normal: d0, color: color),
                VRSceneVertex(position: d1, normal: d1, color: color),
                VRSceneVertex(position: d1 + up, normal: d1, color: color),
                VRSceneVertex(position: d0 + up, normal: d0, color: color)
            )
            mesh.addTriangle(
                VRSceneVertex(position: up, normal: up, color: color),
                VRSceneVertex(position: d0 + up, normal: up, color: color),
                VRSceneVertex(position: d1 + up, normal: up, color: color)
            )
            mesh.addTriangle(
                VRSceneVertex(position: .zero, normal: -up, color: color),
                VRSceneVertex(position: d1, normal: -up, color: color),
                VRSceneVertex(position: d0, normal: -up, color: color)
            )
        }
        return mesh
    }

    /// Torus in the xy plane around the origin, facing +Z.
    static func torus(majorRadius: Float, minorRadius: Float, segments: Int, sides: Int, color: UInt32) -> VRMesh {
        var mesh = VRMesh()
        func vertex(_ i: Int, _ j: Int) -> VRSceneVertex {
            let u = Float(i) / Float(segments) * 2 * .pi
            let v = Float(j) / Float(sides) * 2 * .pi
            let ring = SIMD3(cos(u), sin(u), 0)
            let normal = ring * cos(v) + SIMD3(0, 0, sin(v))
            return VRSceneVertex(position: ring * majorRadius + normal * minorRadius, normal: normal, color: color)
        }
        for i in 0..<segments {
            for j in 0..<sides {
                mesh.addQuad(vertex(i, j), vertex(i + 1, j), vertex(i + 1, j + 1), vertex(i, j + 1))
            }
        }
        return mesh
    }

    /// Square floor at y = 0 facing up. The grid lines come from the shader.
    static func floor(halfExtent: Float) -> VRMesh {
        var mesh = VRMesh()
        let n = SIMD3<Float>(0, 1, 0)
        let corners = [SIMD3(-halfExtent, 0, halfExtent), SIMD3(halfExtent, 0, halfExtent),
                       SIMD3(halfExtent, 0, -halfExtent), SIMD3(-halfExtent, 0, -halfExtent)]
        let v = corners.map { VRSceneVertex(position: $0, normal: n, color: VRPalette.white) }
        mesh.addQuad(v[0], v[1], v[2], v[3])
        return mesh
    }

    /// Unit cube from y = 0 to 1, centred in x and z, with faces pointing inward.
    static func room() -> VRMesh {
        var mesh = box(color: VRPalette.white)
        for i in mesh.vertices.indices {
            var v = mesh.vertices[i]
            v.py += 0.5
            v.nx = -v.nx
            v.ny = -v.ny
            v.nz = -v.nz
            mesh.vertices[i] = v
        }
        var flipped = VRMesh()
        var k = 0
        while k + 2 < mesh.indices.count {
            flipped.addTriangle(
                mesh.vertices[Int(mesh.indices[k])],
                mesh.vertices[Int(mesh.indices[k + 1])],
                mesh.vertices[Int(mesh.indices[k + 2])]
            )
            k += 3
        }
        return flipped
    }

    /// Unit-radius open cylinder from y = 0 to 1, normals outward. Drawn
    /// without culling so the wall shows from inside.
    static func openCylinder(segments: Int) -> VRMesh {
        var mesh = VRMesh()
        let up = SIMD3<Float>(0, 1, 0)
        for i in 0..<segments {
            let a0 = Float(i) / Float(segments) * 2 * .pi
            let a1 = Float(i + 1) / Float(segments) * 2 * .pi
            let d0 = SIMD3(cos(a0), 0, sin(a0))
            let d1 = SIMD3(cos(a1), 0, sin(a1))
            mesh.addQuad(
                VRSceneVertex(position: d0, normal: d0, color: VRPalette.white),
                VRSceneVertex(position: d1, normal: d1, color: VRPalette.white),
                VRSceneVertex(position: d1 + up, normal: d1, color: VRPalette.white),
                VRSceneVertex(position: d0 + up, normal: d0, color: VRPalette.white)
            )
        }
        return mesh
    }

    /// Unit disc at y = 0 facing up.
    static func disc(segments: Int, color: UInt32) -> VRMesh {
        var mesh = VRMesh()
        let up = SIMD3<Float>(0, 1, 0)
        for i in 0..<segments {
            let a0 = Float(i) / Float(segments) * 2 * .pi
            let a1 = Float(i + 1) / Float(segments) * 2 * .pi
            mesh.addTriangle(
                VRSceneVertex(position: .zero, normal: up, color: color),
                VRSceneVertex(position: SIMD3(cos(a0), 0, sin(a0)), normal: up, color: color),
                VRSceneVertex(position: SIMD3(cos(a1), 0, sin(a1)), normal: up, color: color)
            )
        }
        return mesh
    }
}

/// Shading model, matched by value in the scene fragment shader.
enum VRMaterial: Int {
    case lit = 0
    case emissive = 1
    case floorGrid = 2
    case roomGrid = 3
    case boundary = 4
    /// Vertex color with a head-lamp falloff to black. Used by Minecraft voxels.
    case voxel = 5
}

enum VRSceneKind: String, CaseIterable, Codable, Identifiable {
    case studio
    case calibration
    case minecraft

    var id: String { rawValue }

    var title: String {
        switch self {
        case .studio: return "Studio"
        case .calibration: return "Calibration"
        case .minecraft: return "Minecraft"
        }
    }

    /// Menu button label when this scene is the destination of a cycle.
    var menuTitle: String {
        switch self {
        case .studio: return "Studio"
        case .calibration: return "Calibrate lenses"
        case .minecraft: return "Minecraft"
        }
    }

    var next: VRSceneKind {
        let all = Self.allCases
        let index = all.firstIndex(of: self) ?? 0
        return all[(index + 1) % all.count]
    }
}

struct VRSceneObject {
    struct Orbit {
        var center: SIMD3<Float>
        var radius: Float
        var period: Double
        var phase: Double
    }

    var mesh: VRMeshKind
    var material: VRMaterial
    var position: SIMD3<Float>
    var rotation: simd_quatf = VRMath.identityRotation
    var scale: SIMD3<Float>
    var color: UInt32
    /// Extra brightness for emissive materials.
    var glow: Float = 0
    /// Rotation vector per second.
    var spin: SIMD3<Float> = .zero
    var bobAmplitude: Float = 0
    var orbit: Orbit?

    func position(at time: Double) -> SIMD3<Float> {
        var p = position
        if let orbit {
            let angle = (time / orbit.period + orbit.phase) * 2 * .pi
            p = orbit.center + SIMD3(Float(sin(angle)), 0, Float(-cos(angle))) * orbit.radius
        }
        if bobAmplitude > 0 {
            p.y += bobAmplitude * Float(sin(time * 1.3))
        }
        return p
    }

    func modelMatrix(at time: Double) -> simd_float4x4 {
        let spun = simd_length(spin) > 0
            ? (VRMath.rotation(fromVector: spin * Float(time.truncatingRemainder(dividingBy: 3600))) * rotation).normalized
            : rotation
        return VRPose(rotation: spun, position: position(at: time)).matrix * VRMath.scale(scale)
    }
}

/// What each scene contains, in scene coordinates (floor at y = 0, forward -Z).
enum VRSceneLayout {
    static let beaconOrbit = VRSceneObject.Orbit(center: SIMD3(0, 1.55, 0), radius: 2.2, period: 24, phase: 0.1)

    /// World-locked scene picker beside the plinth. Yaw faces the origin so
    /// looking at the ornament straight ahead does not cover the buttons.
    static let sceneSignCenter = SIMD3<Float>(-0.72, 1.3, -1.38)

    static var sceneSignPlacement: VRPanelPlacement {
        VRPanelPlacement(
            center: sceneSignCenter,
            rotation: VRMath.rotationY(atan2(-sceneSignCenter.x, -sceneSignCenter.z)),
            size: VRPanelLayouts.sceneSignSize
        )
    }

    static func objects(for scene: VRSceneKind, reduced: Bool) -> [VRSceneObject] {
        switch scene {
        case .studio: return studio(reduced: reduced)
        case .calibration: return calibration()
        case .minecraft: return []
        }
    }

    static func beaconPosition(at time: Double) -> SIMD3<Float> {
        beacon.position(at: time)
    }

    private static let beacon = VRSceneObject(
        mesh: .sphere, material: .emissive, position: .zero, scale: SIMD3(repeating: 0.07),
        color: VRPalette.beacon, glow: 1.6, orbit: beaconOrbit
    )

    private static func studio(reduced: Bool) -> [VRSceneObject] {
        var objects: [VRSceneObject] = [
            VRSceneObject(mesh: .floor, material: .floorGrid, position: .zero, scale: SIMD3(repeating: 1), color: VRPalette.floor),
            VRSceneObject(mesh: .cylinder, material: .lit, position: SIMD3(0, 0, -1.8), scale: SIMD3(0.22, 1.0, 0.22), color: VRPalette.plinth),
            VRSceneObject(
                mesh: .icosahedron, material: .lit, position: SIMD3(0, 1.32, -1.8),
                scale: SIMD3(repeating: 0.17), color: VRPalette.coral, spin: SIMD3(0.15, 0.6, 0.1), bobAmplitude: 0.03
            ),
            VRSceneObject(mesh: .cube, material: .lit, position: SIMD3(-1.4, 0.25, -2.6), rotation: VRMath.rotationY(0.4), scale: SIMD3(repeating: 0.5), color: VRPalette.amber),
            VRSceneObject(mesh: .cube, material: .lit, position: SIMD3(1.6, 0.25, -3.4), rotation: VRMath.rotationY(-0.3), scale: SIMD3(repeating: 0.5), color: VRPalette.sky),
            VRSceneObject(mesh: .cube, material: .lit, position: SIMD3(-3.2, 0.5, -6.0), rotation: VRMath.rotationY(0.2), scale: SIMD3(repeating: 1.0), color: VRPalette.violet),
            VRSceneObject(mesh: .cube, material: .lit, position: SIMD3(2.6, 1.5, -7.0), rotation: VRMath.rotationY(-0.5), scale: SIMD3(0.6, 3.0, 0.15), color: VRPalette.slate),
            VRSceneObject(
                mesh: .torus, material: .emissive, position: SIMD3(0, 4.2, -15),
                scale: SIMD3(repeating: 2.4), color: VRPalette.rose, glow: 1.2, spin: SIMD3(0, 0, 0.1)
            ),
            beacon,
        ]
        objects.append(contentsOf: sceneSignPost)
        let pillarCount = reduced ? 8 : 16
        for i in 0..<pillarCount {
            let angle = Float(i) / Float(pillarCount) * 2 * .pi + 0.1
            objects.append(VRSceneObject(
                mesh: .cylinder, material: .lit,
                position: SIMD3(9 * sin(angle), 0, -9 * cos(angle)),
                scale: SIMD3(0.18, 3.5, 0.18), color: VRPalette.stone
            ))
        }
        return objects
    }

    private static var sceneSignPost: [VRSceneObject] {
        let placement = sceneSignPlacement
        let postHeight = max(0.05, placement.center.y - placement.size.y / 2)
        let boardCenter = placement.center + placement.rotation.act(SIMD3(0, 0, -0.02))
        return [
            VRSceneObject(
                mesh: .cylinder, material: .lit,
                position: SIMD3(placement.center.x, 0, placement.center.z),
                scale: SIMD3(0.04, postHeight, 0.04), color: VRPalette.stone
            ),
            VRSceneObject(
                mesh: .cube, material: .lit, position: boardCenter, rotation: placement.rotation,
                scale: SIMD3(placement.size.x + 0.04, placement.size.y + 0.04, 0.03),
                color: VRPalette.slate
            ),
        ]
    }

    private static func calibration() -> [VRSceneObject] {
        [
            VRSceneObject(mesh: .room, material: .roomGrid, position: .zero, scale: SIMD3(4, 3, 4), color: VRPalette.floor),
            VRSceneObject(mesh: .sphere, material: .emissive, position: SIMD3(0, 1.6, -1.95), scale: SIMD3(repeating: 0.03), color: VRPalette.coral, glow: 1),
        ]
    }
}
