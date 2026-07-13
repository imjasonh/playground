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
    /// Ignore depth samples beyond this range (noisy and budget-hungry).
    static let maxDepthMeters: Float = 5
    static let integrationInterval: TimeInterval = 0.2
    /// Depth-map sampling stride (256×192 map → ~12k samples per tick).
    static let depthStride = 2
    /// Chunk meshes rebuilt per integration tick.
    static let rebuildBudgetPerTick = 24

    @Published private(set) var runState: RunState = .idle
    @Published private(set) var statusMessage = "Sweep the phone around to fill the world with voxels."
    @Published private(set) var voxelCount = 0
    @Published private(set) var usingSceneDepth = false
    @Published private(set) var voxelSize: Float = VoxelSizeMapping.defaultSize
    @Published private(set) var isFrozen = false
    @Published private(set) var showsCameraFeed = true

    let arView: ARSCNView

    private let processingQueue = DispatchQueue(label: "voxel-world.processing", qos: .userInitiated)
    /// Confined to `processingQueue` after init.
    private var grid = VoxelGrid(voxelSize: VoxelSizeMapping.defaultSize)
    /// Chunks needing re-mesh because voxels appeared (processingQueue).
    private var structuralDirty: Set<VoxelChunkKey> = []
    /// Chunks whose voxel colors were refined; rebuilt with leftover budget.
    private var colorDirty: Set<VoxelChunkKey> = []
    /// Main-thread only.
    private var chunkNodes: [VoxelChunkKey: SCNNode] = [:]
    private var lastIntegrationTime: TimeInterval = 0
    private var isIntegrating = false
    private var savedBackgroundContents: Any?
    private var backgroundHidden = false
    private var hasRunBefore = false

    override init() {
        let view = ARSCNView(frame: .zero)
        view.scene = SCNScene()
        view.automaticallyUpdatesLighting = false
        view.accessibilityIdentifier = "voxelWorldARView"
        arView = view
        super.init()
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

    // MARK: - Controls

    /// Changing the voxel size clears the world; it refills as you look around.
    func updateVoxelSize(_ size: Float) {
        let clamped = min(max(size, VoxelSizeMapping.minimumSize), VoxelSizeMapping.maximumSize)
        voxelSize = clamped
        processingQueue.async { [weak self] in
            guard let self, self.grid.voxelSize != clamped else { return }
            self.grid = VoxelGrid(voxelSize: clamped)
            self.structuralDirty.removeAll()
            self.colorDirty.removeAll()
            DispatchQueue.main.async {
                self.removeAllChunkNodes()
                self.voxelCount = 0
            }
        }
    }

    func resetVoxels() {
        processingQueue.async { [weak self] in
            guard let self else { return }
            self.grid.removeAll()
            self.structuralDirty.removeAll()
            self.colorDirty.removeAll()
            DispatchQueue.main.async {
                self.removeAllChunkNodes()
                self.voxelCount = 0
                if self.runState == .running {
                    self.statusMessage = "Cleared — sweep the phone to voxelize again."
                }
            }
        }
    }

    /// Frozen: stop adding/updating voxels but keep tracking, so you can walk
    /// around the voxel world you've built.
    func updateFrozen(_ frozen: Bool) {
        isFrozen = frozen
    }

    /// Hide the live camera feed to see only the voxel reconstruction.
    func updateShowsCameraFeed(_ show: Bool) {
        showsCameraFeed = show
        applyBackgroundVisibility()
    }

    /// Called on every frame: ARSCNView installs the camera feed as the scene
    /// background on its own, so hiding must re-assert against the *actual*
    /// current contents, not just our flag.
    private func applyBackgroundVisibility() {
        if showsCameraFeed {
            if backgroundHidden {
                arView.scene.background.contents = savedBackgroundContents
                backgroundHidden = false
            }
        } else if (arView.scene.background.contents as? UIColor) != UIColor.black {
            savedBackgroundContents = arView.scene.background.contents
            arView.scene.background.contents = UIColor.black
            backgroundHidden = true
        }
    }

    private func removeAllChunkNodes() {
        for node in chunkNodes.values {
            node.removeFromParentNode()
        }
        chunkNodes.removeAll()
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
                    guard depth.isFinite, depth > 0.05, depth < Self.maxDepthMeters else { continue }

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
        } else if let featurePoints {
            for point in featurePoints.prefix(2048) {
                guard let projected = VoxelProjection.pixel(
                    worldPoint: point,
                    intrinsics: intrinsics,
                    cameraTransform: cameraTransform
                ), projected.depthMeters < Self.maxDepthMeters else { continue }
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
        let sizeLabel = VoxelSizeMapping.label(for: grid.voxelSize)
        DispatchQueue.main.async { [weak self] in
            guard let self, self.runState == .running else { return }
            self.voxelCount = count
            if budgetHit {
                self.statusMessage = "Voxel budget full (\(Self.maxVoxels)) — Reset or use bigger voxels."
            } else if !self.isFrozen {
                self.statusMessage = self.usingSceneDepth
                    ? "Voxelizing at \(sizeLabel) — sweep to fill in more of the world."
                    : "Voxelizing feature points at \(sizeLabel) — move slowly over textured surfaces."
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

// MARK: - ARSessionDelegate (main thread)

extension VoxelWorldSession: ARSessionDelegate {
    func session(_ session: ARSession, didUpdate frame: ARFrame) {
        applyBackgroundVisibility()

        guard !isFrozen, !isIntegrating else { return }
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
