import ARKit
import AVFoundation
import SceneKit
import UIKit
import simd

/// ARKit world-tracking session that voxelizes what the camera sees.
///
/// Every ~0.2 s one frame is integrated: LiDAR depth pixels (or, without
/// LiDAR, sparse tracked feature points) are unprojected into world space,
/// quantized into a `VoxelGrid`, and colored from the camera image at that
/// pixel. Chunks whose voxels changed are re-meshed and swapped into the
/// SceneKit scene, so the voxel world accumulates and persists as you move.
/// The camera photo is not shown. Every pixel is drawn as a chunky palette
/// block the size of a voxel at that pixel's depth, and the voxel mesh
/// draws in front.
final class VoxelWorldSession: NSObject, ObservableObject {
    enum RunState: Equatable {
        case idle
        case unsupported
        case requestingPermission
        case permissionDenied
        case running
        case failed(String)
    }

    /// Hard cap so dense LiDAR scans can't grow geometry without bound.
    static let maxVoxels = 80_000
    /// Farthest depth sample to keep. Apple's LiDAR scanner reports nothing
    /// past 5 meters, so this is the hardware maximum.
    static let maxDepthMeters: Float = 5
    /// Fixed block edge. 10 cm is the smallest size that stays crisp on the
    /// 256×192 depth map. Smaller blocks turn sensor noise into fuzzy walls.
    static let voxelEdgeMeters: Float = 0.10
    static let integrationInterval: TimeInterval = 0.2
    /// Depth-map sampling stride (256×192 map → ~12k samples per tick).
    static let depthStride = 2
    /// Chunk meshes rebuilt per integration tick.
    static let rebuildBudgetPerTick = 24

    @Published private(set) var runState: RunState = .idle
    @Published private(set) var statusMessage = "Sweep the phone around to fill the world with voxels."
    @Published private(set) var voxelCount = 0
    @Published private(set) var usingSceneDepth = false
    @Published private(set) var isSavingPhoto = false

    let arView: ARSCNView

    private let processingQueue = DispatchQueue(label: "voxel-world.processing", qos: .userInitiated)
    /// Confined to `processingQueue` after init.
    private var grid = VoxelGrid(voxelSize: VoxelWorldSession.voxelEdgeMeters)
    /// Chunks needing re-mesh because voxels appeared (processingQueue).
    private var structuralDirty: Set<VoxelChunkKey> = []
    /// Chunks whose voxel colors were refined; rebuilt with leftover budget.
    private var colorDirty: Set<VoxelChunkKey> = []
    /// Main-thread only.
    private var chunkNodes: [VoxelChunkKey: SCNNode] = [:]
    private var lastIntegrationTime: TimeInterval = 0
    private var isIntegrating = false
    private var hasRunBefore = false
    /// Keeps a save confirmation on screen while integration keeps publishing.
    private var suppressStatusUntil = Date.distantPast
    private let farFieldQueue = DispatchQueue(label: "voxel-world.far-field", qos: .userInitiated)
    private let farFieldCompositor = FarFieldCompositor()
    /// Main-thread only.
    private var pendingFarField: FarFieldTexture?
    /// Main-thread only. The far shell, parented to the AR camera.
    private var farFieldNode: SCNNode?
    /// Main-thread only. Drops camera frames while one composite is in flight.
    private var farFieldQueued = false

    override init() {
        let view = ARSCNView(frame: .zero)
        view.scene = SCNScene()
        view.automaticallyUpdatesLighting = false
        view.accessibilityIdentifier = "voxelWorldARView"
        arView = view
        super.init()
        view.delegate = self
    }

    // MARK: - Lifecycle

    func start() {
        switch runState {
        case .running, .requestingPermission:
            return
        default:
            break
        }

        guard ARWorldTrackingConfiguration.isSupported else {
            runState = .unsupported
            statusMessage = "ARKit world tracking isn't available here (Simulator or unsupported device)."
            return
        }

        runState = .requestingPermission
        statusMessage = "Requesting camera access…"

        Task { @MainActor in
            let granted = await Self.requestCameraAccess()
            guard granted else {
                self.runState = .permissionDenied
                self.statusMessage = "Camera access is required. Enable it in Settings."
                return
            }
            self.runSession()
        }
    }

    func stop() {
        arView.session.pause()
        if runState == .running {
            runState = .idle
            statusMessage = "Stopped."
        }
    }

    private func runSession() {
        let configuration = ARWorldTrackingConfiguration()
        configuration.worldAlignment = .gravity

        var usesDepth = false
        if ARWorldTrackingConfiguration.supportsFrameSemantics(.smoothedSceneDepth) {
            configuration.frameSemantics.insert(.smoothedSceneDepth)
            usesDepth = true
        } else if ARWorldTrackingConfiguration.supportsFrameSemantics(.sceneDepth) {
            configuration.frameSemantics.insert(.sceneDepth)
            usesDepth = true
        }
        usingSceneDepth = usesDepth

        arView.session.delegate = self
        // Resume (relocalize) after the first run so voxels captured earlier
        // stay aligned with the world instead of jumping to a new origin.
        let options: ARSession.RunOptions = hasRunBefore ? [] : [.resetTracking, .removeExistingAnchors]
        arView.session.run(configuration, options: options)
        hasRunBefore = true
        runState = .running
        statusMessage = usesDepth
            ? "LiDAR depth active — sweep the phone to voxelize the room."
            : "No LiDAR — voxelizing sparse feature points. Move slowly over textured surfaces."
    }

    // MARK: - Photo

    /// Writes the current frame, camera and voxels, to the photo library.
    func saveCurrentFrame() {
        guard !isSavingPhoto else { return }
        guard runState == .running else {
            statusMessage = "Camera isn't running."
            return
        }
        installPendingFarField()
        let image = arView.snapshot()
        isSavingPhoto = true
        statusMessage = "Saving…"
        Task { @MainActor in
            do {
                try await VoxelPhotoSaver.saveJPEG(image)
                self.statusMessage = "Saved to Photos."
                self.suppressStatusUntil = Date().addingTimeInterval(2.5)
            } catch {
                self.statusMessage = error.localizedDescription
                self.suppressStatusUntil = Date().addingTimeInterval(4)
            }
            self.isSavingPhoto = false
        }
    }

    private static func requestCameraAccess() async -> Bool {
        switch AVCaptureDevice.authorizationStatus(for: .video) {
        case .authorized:
            return true
        case .notDetermined:
            return await AVCaptureDevice.requestAccess(for: .video)
        default:
            return false
        }
    }

    // MARK: - Frame integration (processing queue)

    private func integrate(
        intrinsics: simd_float3x3,
        cameraTransform: simd_float4x4,
        capturedImage: CVPixelBuffer,
        depthMap: CVPixelBuffer?,
        confidenceMap: CVPixelBuffer?,
        featurePoints: [SIMD3<Float>]?
    ) {
        var touchedStructural = Set<VoxelChunkKey>()
        var touchedColor = Set<VoxelChunkKey>()
        var budgetHit = false

        CVPixelBufferLockBaseAddress(capturedImage, .readOnly)
        defer { CVPixelBufferUnlockBaseAddress(capturedImage, .readOnly) }

        guard
            CVPixelBufferGetPlaneCount(capturedImage) >= 2,
            let lumaBaseRaw = CVPixelBufferGetBaseAddressOfPlane(capturedImage, 0),
            let chromaBaseRaw = CVPixelBufferGetBaseAddressOfPlane(capturedImage, 1)
        else {
            return
        }
        let luma = lumaBaseRaw.assumingMemoryBound(to: UInt8.self)
        let chroma = chromaBaseRaw.assumingMemoryBound(to: UInt8.self)
        let lumaBytesPerRow = CVPixelBufferGetBytesPerRowOfPlane(capturedImage, 0)
        let chromaBytesPerRow = CVPixelBufferGetBytesPerRowOfPlane(capturedImage, 1)
        let imageWidth = CVPixelBufferGetWidthOfPlane(capturedImage, 0)
        let imageHeight = CVPixelBufferGetHeightOfPlane(capturedImage, 0)
        let chromaWidth = CVPixelBufferGetWidthOfPlane(capturedImage, 1)
        let chromaHeight = CVPixelBufferGetHeightOfPlane(capturedImage, 1)

        func sampleColor(imageX: Int, imageY: Int) -> SIMD3<Float>? {
            guard imageX >= 0, imageX < imageWidth, imageY >= 0, imageY < imageHeight else {
                return nil
            }
            let y = luma[imageY * lumaBytesPerRow + imageX]
            let cx = min(imageX / 2, chromaWidth - 1)
            let cy = min(imageY / 2, chromaHeight - 1)
            let cb = chroma[cy * chromaBytesPerRow + cx * 2]
            let cr = chroma[cy * chromaBytesPerRow + cx * 2 + 1]
            return VoxelColorConversion.rgb(y: y, cb: cb, cr: cr)
        }

        func record(_ result: VoxelGrid.AddResult) {
            switch result {
            case .added(let key):
                touchedStructural.formUnion(grid.affectedChunks(around: key))
            case .updated(let key):
                touchedColor.insert(grid.chunkKey(for: key))
            case .rejectedBudget:
                budgetHit = true
            case .rejectedInvalid:
                break
            }
        }

        if let depthMap {
            CVPixelBufferLockBaseAddress(depthMap, .readOnly)
            if let confidenceMap {
                CVPixelBufferLockBaseAddress(confidenceMap, .readOnly)
            }
            defer {
                if let confidenceMap {
                    CVPixelBufferUnlockBaseAddress(confidenceMap, .readOnly)
                }
                CVPixelBufferUnlockBaseAddress(depthMap, .readOnly)
            }

            guard let depthBaseRaw = CVPixelBufferGetBaseAddress(depthMap) else { return }
            let depthWidth = CVPixelBufferGetWidth(depthMap)
            let depthHeight = CVPixelBufferGetHeight(depthMap)
            let depthBytesPerRow = CVPixelBufferGetBytesPerRow(depthMap)

            var confidenceBase: UnsafePointer<UInt8>?
            var confidenceBytesPerRow = 0
            if let confidenceMap,
               CVPixelBufferGetWidth(confidenceMap) == depthWidth,
               CVPixelBufferGetHeight(confidenceMap) == depthHeight,
               let base = CVPixelBufferGetBaseAddress(confidenceMap) {
                confidenceBase = UnsafePointer(base.assumingMemoryBound(to: UInt8.self))
                confidenceBytesPerRow = CVPixelBufferGetBytesPerRow(confidenceMap)
            }

            let scaleX = Float(imageWidth) / Float(depthWidth)
            let scaleY = Float(imageHeight) / Float(depthHeight)

            for depthY in stride(from: 0, to: depthHeight, by: Self.depthStride) {
                let depthRow = (depthBaseRaw + depthY * depthBytesPerRow)
                    .assumingMemoryBound(to: Float32.self)
                for depthX in stride(from: 0, to: depthWidth, by: Self.depthStride) {
                    let depth = depthRow[depthX]
                    guard depth.isFinite,
                          depth > FarFieldPixelizer.minimumDepth,
                          depth <= Self.maxDepthMeters else { continue }

                    if let confidenceBase {
                        let confidence = confidenceBase[depthY * confidenceBytesPerRow + depthX]
                        guard confidence >= UInt8(ARConfidenceLevel.medium.rawValue) else { continue }
                    }

                    let pixelX = (Float(depthX) + 0.5) * scaleX
                    let pixelY = (Float(depthY) + 0.5) * scaleY
                    guard let color = sampleColor(imageX: Int(pixelX), imageY: Int(pixelY)) else { continue }
                    guard let world = VoxelProjection.worldPoint(
                        pixel: SIMD2<Float>(pixelX, pixelY),
                        depthMeters: depth,
                        intrinsics: intrinsics,
                        cameraTransform: cameraTransform
                    ) else { continue }

                    record(grid.addSample(worldPoint: world, color: color, maxVoxels: Self.maxVoxels))
                }
            }

            // Carve pass: any existing voxel the camera can now see *through*
            // (observed surface well behind it) accrues a miss and is removed
            // after a few consecutive misses. This is what lets moved objects
            // and depth-noise floaters disappear instead of leaving trails.
            let existingKeys = grid.chunks.values.flatMap { $0.keys }
            for key in existingKeys {
                let center = grid.center(of: key)
                guard let projected = VoxelProjection.pixel(
                    worldPoint: center,
                    intrinsics: intrinsics,
                    cameraTransform: cameraTransform
                ) else { continue }

                let depthX = Int((projected.pixel.x / scaleX).rounded(.down))
                let depthY = Int((projected.pixel.y / scaleY).rounded(.down))
                guard depthX >= 0, depthX < depthWidth, depthY >= 0, depthY < depthHeight else { continue }

                if let confidenceBase {
                    let confidence = confidenceBase[depthY * confidenceBytesPerRow + depthX]
                    guard confidence >= UInt8(ARConfidenceLevel.medium.rawValue) else { continue }
                }
                let observed = (depthBaseRaw + depthY * depthBytesPerRow)
                    .assumingMemoryBound(to: Float32.self)[depthX]

                switch VoxelCarver.classify(
                    voxelDepth: projected.depthMeters,
                    observedDepth: observed,
                    voxelSize: grid.voxelSize
                ) {
                case .freeSpace:
                    if grid.registerMiss(at: key) {
                        touchedStructural.formUnion(grid.affectedChunks(around: key))
                    }
                case .confirmed:
                    grid.registerConfirmation(at: key)
                case .unknown:
                    break
                }
            }
        } else if let featurePoints {
            for point in featurePoints.prefix(2048) {
                guard let projected = VoxelProjection.pixel(
                    worldPoint: point,
                    intrinsics: intrinsics,
                    cameraTransform: cameraTransform
                ), projected.depthMeters <= Self.maxDepthMeters else { continue }
                guard let color = sampleColor(
                    imageX: Int(projected.pixel.x),
                    imageY: Int(projected.pixel.y)
                ) else { continue }

                record(grid.addSample(worldPoint: point, color: color, maxVoxels: Self.maxVoxels))
            }
        }

        structuralDirty.formUnion(touchedStructural)
        colorDirty.formUnion(touchedColor)
        rebuildDirtyChunks()
        publishStatus(budgetHit: budgetHit)
    }

    private func rebuildDirtyChunks() {
        var toRebuild: [VoxelChunkKey] = []
        while toRebuild.count < Self.rebuildBudgetPerTick, let chunk = structuralDirty.popFirst() {
            toRebuild.append(chunk)
            colorDirty.remove(chunk)
        }
        while toRebuild.count < Self.rebuildBudgetPerTick, let chunk = colorDirty.popFirst() {
            toRebuild.append(chunk)
        }
        guard !toRebuild.isEmpty else { return }

        var geometries: [(VoxelChunkKey, SCNGeometry?)] = []
        for chunk in toRebuild {
            let mesh = VoxelMesher.mesh(
                voxels: grid.voxels(in: chunk),
                voxelSize: grid.voxelSize,
                isOccupied: { self.grid.isOccupied($0) }
            )
            geometries.append((chunk, Self.makeGeometry(from: mesh)))
        }

        DispatchQueue.main.async { [weak self] in
            self?.applyGeometries(geometries)
        }
    }

    private func publishStatus(budgetHit: Bool) {
        let count = grid.voxelCount
        DispatchQueue.main.async { [weak self] in
            guard let self, self.runState == .running else { return }
            self.voxelCount = count
            guard !self.isSavingPhoto, Date() >= self.suppressStatusUntil else { return }
            if budgetHit {
                self.statusMessage = "Voxel budget full (\(Self.maxVoxels))."
            } else {
                self.statusMessage = self.usingSceneDepth
                    ? "Voxelizing. Sweep to fill in more of the world."
                    : "Voxelizing feature points. Move slowly over textured surfaces."
            }
        }
    }

    // MARK: - SceneKit (main thread)

    private func applyGeometries(_ geometries: [(VoxelChunkKey, SCNGeometry?)]) {
        for (chunk, geometry) in geometries {
            if let geometry {
                if let node = chunkNodes[chunk] {
                    node.geometry = geometry
                } else {
                    let node = SCNNode(geometry: geometry)
                    chunkNodes[chunk] = node
                    arView.scene.rootNode.addChildNode(node)
                }
            } else if let node = chunkNodes.removeValue(forKey: chunk) {
                node.removeFromParentNode()
            }
        }
    }

    private static func makeGeometry(from mesh: VoxelMeshData) -> SCNGeometry? {
        guard !mesh.isEmpty else { return nil }

        let positionData = mesh.positions.withUnsafeBufferPointer { Data(buffer: $0) }
        let normalData = mesh.normals.withUnsafeBufferPointer { Data(buffer: $0) }
        let colorData = mesh.colors.withUnsafeBufferPointer { Data(buffer: $0) }
        let indexData = mesh.indices.withUnsafeBufferPointer { Data(buffer: $0) }

        let positionSource = SCNGeometrySource(
            data: positionData,
            semantic: .vertex,
            vectorCount: mesh.positions.count,
            usesFloatComponents: true,
            componentsPerVector: 3,
            bytesPerComponent: MemoryLayout<Float>.size,
            dataOffset: 0,
            dataStride: MemoryLayout<SIMD3<Float>>.stride
        )
        let normalSource = SCNGeometrySource(
            data: normalData,
            semantic: .normal,
            vectorCount: mesh.normals.count,
            usesFloatComponents: true,
            componentsPerVector: 3,
            bytesPerComponent: MemoryLayout<Float>.size,
            dataOffset: 0,
            dataStride: MemoryLayout<SIMD3<Float>>.stride
        )
        let colorSource = SCNGeometrySource(
            data: colorData,
            semantic: .color,
            vectorCount: mesh.colors.count,
            usesFloatComponents: true,
            componentsPerVector: 4,
            bytesPerComponent: MemoryLayout<Float>.size,
            dataOffset: 0,
            dataStride: MemoryLayout<SIMD4<Float>>.stride
        )
        let element = SCNGeometryElement(
            data: indexData,
            primitiveType: .triangles,
            primitiveCount: mesh.indices.count / 3,
            bytesPerIndex: MemoryLayout<UInt32>.size
        )

        let geometry = SCNGeometry(
            sources: [positionSource, normalSource, colorSource],
            elements: [element]
        )
        let material = SCNMaterial()
        material.lightingModel = .constant
        material.isDoubleSided = true
        geometry.materials = [material]
        return geometry
    }
}

// MARK: - Camera frames

extension VoxelWorldSession: ARSCNViewDelegate {
    func renderer(_: SCNSceneRenderer, willRenderScene _: SCNScene, atTime _: TimeInterval) {
        // ARKit puts the camera feed on the background every frame. The chunk
        // plane covers the view; black keeps a gap from showing the photo.
        arView.scene.background.contents = UIColor.black
    }

    func session(_ session: ARSession, didUpdate frame: ARFrame) {
        installPendingFarField()
        scheduleFarField(frame)
        guard !isIntegrating else { return }
        guard frame.timestamp - lastIntegrationTime >= Self.integrationInterval else { return }
        lastIntegrationTime = frame.timestamp
        isIntegrating = true

        let intrinsics = frame.camera.intrinsics
        let cameraTransform = frame.camera.transform
        let capturedImage = frame.capturedImage
        let depthData = frame.smoothedSceneDepth ?? frame.sceneDepth
        let depthMap = depthData?.depthMap
        let confidenceMap = depthData?.confidenceMap
        // Feature points only matter on devices without scene depth.
        let featurePoints = depthMap == nil ? frame.rawFeaturePoints?.points : nil

        processingQueue.async { [weak self] in
            defer {
                DispatchQueue.main.async { self?.isIntegrating = false }
            }
            self?.integrate(
                intrinsics: intrinsics,
                cameraTransform: cameraTransform,
                capturedImage: capturedImage,
                depthMap: depthMap,
                confidenceMap: confidenceMap,
                featurePoints: featurePoints
            )
        }
    }

    private func scheduleFarField(_ frame: ARFrame) {
        guard !farFieldQueued else { return }
        farFieldQueued = true
        farFieldQueue.async { [weak self] in
            let texture = self?.farFieldCompositor.texture(frame: frame)
            DispatchQueue.main.async {
                guard let self else { return }
                if let texture {
                    self.pendingFarField = texture
                    self.installPendingFarField()
                }
                self.farFieldQueued = false
            }
        }
    }

    /// Places the latest chunk texture on a camera-parented plane just past
    /// the scanner maximum. The texture is opaque. Voxels in front of the
    /// plane still draw; the camera photo does not.
    private func installPendingFarField() {
        guard let texture = pendingFarField else { return }
        guard let cameraNode = arView.pointOfView else { return }

        let fx = texture.intrinsics[0][0]
        let fy = texture.intrinsics[1][1]
        let cx = texture.intrinsics[2][0]
        let cy = texture.intrinsics[2][1]
        guard fx > 0, fy > 0 else { return }

        // Sit just behind the farthest voxel so a block at the depth cap
        // occludes the shell instead of z-fighting it.
        let shellDepth = Self.maxDepthMeters + Self.voxelEdgeMeters + 0.05
        let imageWidth = Float(texture.imageWidth)
        let imageHeight = Float(texture.imageHeight)
        let planeWidth = imageWidth * shellDepth / fx
        let planeHeight = imageHeight * shellDepth / fy
        let centerX = (imageWidth * 0.5 - cx) * shellDepth / fx
        let centerY = -(imageHeight * 0.5 - cy) * shellDepth / fy

        let node: SCNNode
        if let farFieldNode {
            node = farFieldNode
        } else {
            let material = SCNMaterial()
            material.lightingModel = .constant
            material.isDoubleSided = false
            material.readsFromDepthBuffer = true
            material.writesToDepthBuffer = false
            material.diffuse.magnificationFilter = .nearest
            material.diffuse.minificationFilter = .nearest
            material.diffuse.mipFilter = .none
            material.diffuse.wrapS = .clamp
            material.diffuse.wrapT = .clamp
            let plane = SCNPlane(width: CGFloat(planeWidth), height: CGFloat(planeHeight))
            plane.materials = [material]
            let created = SCNNode(geometry: plane)
            created.renderingOrder = 10
            farFieldNode = created
            node = created
        }
        if node.parent != cameraNode {
            node.removeFromParentNode()
            cameraNode.addChildNode(node)
        }
        if let plane = node.geometry as? SCNPlane {
            plane.width = CGFloat(planeWidth)
            plane.height = CGFloat(planeHeight)
            plane.firstMaterial?.diffuse.contents = texture.image
        }
        node.position = SCNVector3(centerX, centerY, -shellDepth)
        pendingFarField = nil
    }

    func session(_ session: ARSession, didFailWithError error: Error) {
        runState = .failed(error.localizedDescription)
        statusMessage = error.localizedDescription
    }

    func sessionWasInterrupted(_ session: ARSession) {
        if runState == .running {
            statusMessage = "Session interrupted…"
        }
    }

    func sessionInterruptionEnded(_ session: ARSession) {
        if runState == .running {
            statusMessage = "Session resumed."
        }
    }
}
