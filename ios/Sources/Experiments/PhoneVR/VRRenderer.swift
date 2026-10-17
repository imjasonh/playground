import CoreVideo
import Foundation
import Metal
import simd

struct VRDrawPanel {
    var texture: MTLTexture
    var uniforms: VRPanelUniforms
}

struct VRPassthroughDraw {
    var luma: MTLTexture
    var chroma: MTLTexture
    var uniforms: VRPassthroughUniforms
}

/// Everything the eye pass draws for one frame.
struct VREyeFrame {
    /// Left then right.
    var eyes: [VREyeUniforms]
    var frame: VRFrameUniforms
    var instances: [VRDrawInstance]
    var boundary: VRInstanceUniforms?
    var panels: [VRDrawPanel]
    var reticle: VRPanelUniforms?
    var passthrough: VRPassthroughDraw?
    var drawSky: Bool
    /// World-space voxel chunk meshes. `voxelUniforms.model` maps them into
    /// scene space (`sceneFromWorld`).
    var voxelChunks: [VRVoxelMeshChunk] = []
    var voxelUniforms: VRInstanceUniforms?
}

/// Everything the final pass needs for one frame.
struct VRFinalFrame {
    /// Left then right.
    var eyes: [VRDistortionEyeUniforms]
    var frame: VRDistortionFrameUniforms
}

/// Metal renderer for phone VR: a stereo eye pass into a two-layer texture,
/// then a final pass that corrects the lenses onto the panel.
///
/// Created on the main thread, then used only from the render thread (and
/// from tests), so it carries no locks.
final class VRRenderer: @unchecked Sendable {
    struct Options {
        var multisample = true
        var singlePassStereo = true
        /// Tile-memory MSAA and depth. The Simulator may not support it.
        var memorylessTargets = true
    }

    enum RendererError: Error, LocalizedError {
        case noCommandQueue
        case missingFunction(String)
        case resource(String)

        var errorDescription: String? {
            switch self {
            case .noCommandQueue: return "Metal couldn't create a command queue."
            case .missingFunction(let name): return "The shader library has no function named \(name)."
            case .resource(let what): return "Metal couldn't allocate \(what)."
            }
        }
    }

    struct EyeTargets {
        let width: Int
        let height: Int
        /// Two-layer array: layer 0 left, layer 1 right. The final pass samples it.
        let color: MTLTexture
        let multisampleColor: MTLTexture?
        let depth: MTLTexture
    }

    private struct GPUMesh {
        let vertices: MTLBuffer
        let indices: MTLBuffer
        let indexCount: Int
    }

    private struct DiscMeshes {
        let buffer: MTLBuffer
        let verticesPerEye: Int
        let key: SIMD4<Float>
    }

    static let eyeColorFormat: MTLPixelFormat = .bgra8Unorm_srgb
    static let drawableFormat: MTLPixelFormat = .bgra8Unorm_srgb
    static let depthFormat: MTLPixelFormat = .depth32Float
    static let maskSegments = 64
    static let discSegments = 96

    let device: MTLDevice
    let commandQueue: MTLCommandQueue
    let usesAmplification: Bool
    let sampleCount: Int
    private let memoryless: Bool
    private let library: MTLLibrary

    private let scenePipeline: MTLRenderPipelineState
    private let boundaryPipeline: MTLRenderPipelineState
    private let skyPipeline: MTLRenderPipelineState
    private let maskPipeline: MTLRenderPipelineState
    private let panelPipeline: MTLRenderPipelineState
    private let reticlePipeline: MTLRenderPipelineState
    private let passthroughPipeline: MTLRenderPipelineState
    private let finalPipeline: MTLRenderPipelineState

    private let opaqueDepth: MTLDepthStencilState
    private let readOnlyDepth: MTLDepthStencilState
    private let maskDepth: MTLDepthStencilState
    private let skyDepth: MTLDepthStencilState
    private let overlayDepth: MTLDepthStencilState

    private let meshes: [VRMeshKind: GPUMesh]
    private let maskDirections: MTLBuffer
    private let maskVertexCount: Int
    private(set) var eyeTargets: EyeTargets?
    private var discs: DiscMeshes?

    static func supportsSinglePassStereo(_ device: MTLDevice) -> Bool {
        device.supportsVertexAmplificationCount(2)
    }

    static func makeLibrary(device: MTLDevice, amplification: Bool) throws -> MTLLibrary {
        let options = MTLCompileOptions()
        options.preprocessorMacros = ["PVR_AMPLIFY": NSNumber(value: amplification ? 1 : 0)]
        return try device.makeLibrary(source: VRShaderSource.source, options: options)
    }

    init(device: MTLDevice, options: Options) throws {
        self.device = device
        guard let queue = device.makeCommandQueue() else { throw RendererError.noCommandQueue }
        queue.label = "PhoneVR"
        commandQueue = queue
        usesAmplification = options.singlePassStereo && Self.supportsSinglePassStereo(device)
        sampleCount = options.multisample && device.supportsTextureSampleCount(4) ? 4 : 1
        memoryless = options.memorylessTargets
        library = try Self.makeLibrary(device: device, amplification: usesAmplification)

        let descriptors = try Self.pipelineDescriptors(
            library: library,
            amplification: usesAmplification,
            sampleCount: sampleCount
        )
        func pipeline(_ name: String) throws -> MTLRenderPipelineState {
            guard let descriptor = descriptors[name] else { throw RendererError.missingFunction(name) }
            return try device.makeRenderPipelineState(descriptor: descriptor)
        }
        scenePipeline = try pipeline("scene")
        boundaryPipeline = try pipeline("boundary")
        skyPipeline = try pipeline("sky")
        maskPipeline = try pipeline("mask")
        panelPipeline = try pipeline("panel")
        reticlePipeline = try pipeline("reticle")
        passthroughPipeline = try pipeline("passthrough")
        finalPipeline = try pipeline("final")

        func depthState(_ compare: MTLCompareFunction, write: Bool) throws -> MTLDepthStencilState {
            let descriptor = MTLDepthStencilDescriptor()
            descriptor.depthCompareFunction = compare
            descriptor.isDepthWriteEnabled = write
            guard let state = device.makeDepthStencilState(descriptor: descriptor) else {
                throw RendererError.resource("a depth state")
            }
            return state
        }
        // Depth is reversed: 1 is the near plane, 0 is infinitely far.
        opaqueDepth = try depthState(.greater, write: true)
        readOnlyDepth = try depthState(.greater, write: false)
        maskDepth = try depthState(.always, write: true)
        skyDepth = try depthState(.greaterEqual, write: false)
        overlayDepth = try depthState(.always, write: false)

        var built: [VRMeshKind: GPUMesh] = [:]
        for kind in VRMeshKind.allCases {
            let mesh = VRMeshFactory.mesh(kind)
            guard let vertices = device.makeBuffer(bytes: mesh.vertices, length: mesh.vertices.count * MemoryLayout<VRSceneVertex>.stride, options: .storageModeShared),
                  let indices = device.makeBuffer(bytes: mesh.indices, length: mesh.indices.count * MemoryLayout<UInt16>.stride, options: .storageModeShared)
            else { throw RendererError.resource("mesh buffers") }
            vertices.label = "mesh \(kind)"
            built[kind] = GPUMesh(vertices: vertices, indices: indices, indexCount: mesh.indices.count)
        }
        meshes = built

        var directions: [SIMD4<Float>] = []
        for i in 0...Self.maskSegments {
            let angle = Float(i) / Float(Self.maskSegments) * 2 * .pi
            directions.append(SIMD4(cos(angle), sin(angle), 0, 0))
            directions.append(SIMD4(cos(angle), sin(angle), 1, 0))
        }
        guard let maskBuffer = device.makeBuffer(bytes: directions, length: directions.count * MemoryLayout<SIMD4<Float>>.stride, options: .storageModeShared) else {
            throw RendererError.resource("the hidden-area mask")
        }
        maskDirections = maskBuffer
        maskVertexCount = directions.count
    }

    /// Pipeline descriptors by name. Tests use these to reflect buffer layouts.
    static func pipelineDescriptors(library: MTLLibrary, amplification: Bool, sampleCount: Int) throws -> [String: MTLRenderPipelineDescriptor] {
        func function(_ name: String) throws -> MTLFunction {
            guard let f = library.makeFunction(name: name) else { throw RendererError.missingFunction(name) }
            return f
        }
        func eyeDescriptor(_ vertex: String, _ fragment: String, label: String, blended: Bool) throws -> MTLRenderPipelineDescriptor {
            let d = MTLRenderPipelineDescriptor()
            d.label = label
            d.vertexFunction = try function(vertex)
            d.fragmentFunction = try function(fragment)
            d.colorAttachments[0].pixelFormat = eyeColorFormat
            d.depthAttachmentPixelFormat = depthFormat
            d.rasterSampleCount = sampleCount
            d.inputPrimitiveTopology = .triangle
            if amplification { d.maxVertexAmplificationCount = 2 }
            if blended { Self.premultipliedBlending(d.colorAttachments[0]) }
            return d
        }
        let scene = try eyeDescriptor("scene_vertex", "scene_fragment", label: "scene", blended: false)
        scene.vertexDescriptor = sceneVertexDescriptor()
        let boundary = try eyeDescriptor("scene_vertex", "boundary_fragment", label: "boundary", blended: true)
        boundary.vertexDescriptor = sceneVertexDescriptor()
        let mask = try eyeDescriptor("mask_vertex", "mask_fragment", label: "mask", blended: false)
        mask.colorAttachments[0].writeMask = []

        let final = MTLRenderPipelineDescriptor()
        final.label = "final"
        final.vertexFunction = try function("final_vertex")
        final.fragmentFunction = try function("final_fragment")
        final.colorAttachments[0].pixelFormat = drawableFormat

        return [
            "scene": scene,
            "boundary": boundary,
            "sky": try eyeDescriptor("sky_vertex", "sky_fragment", label: "sky", blended: false),
            "mask": mask,
            "panel": try eyeDescriptor("panel_vertex", "panel_fragment", label: "panel", blended: true),
            "reticle": try eyeDescriptor("panel_vertex", "reticle_fragment", label: "reticle", blended: true),
            "passthrough": try eyeDescriptor("passthrough_vertex", "passthrough_fragment", label: "passthrough", blended: true),
            "final": final,
        ]
    }

    private static func premultipliedBlending(_ attachment: MTLRenderPipelineColorAttachmentDescriptor) {
        attachment.isBlendingEnabled = true
        attachment.rgbBlendOperation = .add
        attachment.alphaBlendOperation = .add
        attachment.sourceRGBBlendFactor = .one
        attachment.sourceAlphaBlendFactor = .one
        attachment.destinationRGBBlendFactor = .oneMinusSourceAlpha
        attachment.destinationAlphaBlendFactor = .oneMinusSourceAlpha
    }

    private static func sceneVertexDescriptor() -> MTLVertexDescriptor {
        let d = MTLVertexDescriptor()
        d.attributes[0].format = .float3
        d.attributes[0].offset = 0
        d.attributes[0].bufferIndex = 0
        d.attributes[1].format = .float3
        d.attributes[1].offset = 12
        d.attributes[1].bufferIndex = 0
        d.attributes[2].format = .uchar4Normalized
        d.attributes[2].offset = 24
        d.attributes[2].bufferIndex = 0
        d.layouts[0].stride = MemoryLayout<VRSceneVertex>.stride
        d.layouts[0].stepFunction = .perVertex
        return d
    }

    // MARK: - Targets

    /// Eye buffers of the requested size, reallocating only when the size changes.
    @discardableResult
    func ensureEyeTargets(width: Int, height: Int) throws -> EyeTargets {
        if let existing = eyeTargets, existing.width == width, existing.height == height { return existing }
        let color = MTLTextureDescriptor()
        color.textureType = .type2DArray
        color.arrayLength = 2
        color.pixelFormat = Self.eyeColorFormat
        color.width = width
        color.height = height
        color.usage = [.renderTarget, .shaderRead]
        color.storageMode = .private
        guard let colorTexture = device.makeTexture(descriptor: color) else { throw RendererError.resource("eye buffers") }
        colorTexture.label = "eye buffers"

        let layers = usesAmplification ? 2 : 1
        let transientStorage: MTLStorageMode = memoryless ? .memoryless : .private
        var multisampleColor: MTLTexture?
        if sampleCount > 1 {
            let msaa = MTLTextureDescriptor()
            msaa.textureType = usesAmplification ? .type2DMultisampleArray : .type2DMultisample
            msaa.arrayLength = layers
            msaa.sampleCount = sampleCount
            msaa.pixelFormat = Self.eyeColorFormat
            msaa.width = width
            msaa.height = height
            msaa.usage = .renderTarget
            msaa.storageMode = transientStorage
            guard let texture = device.makeTexture(descriptor: msaa) else { throw RendererError.resource("multisample eye buffers") }
            multisampleColor = texture
        }

        let depth = MTLTextureDescriptor()
        if sampleCount > 1 {
            depth.textureType = usesAmplification ? .type2DMultisampleArray : .type2DMultisample
            depth.sampleCount = sampleCount
        } else {
            depth.textureType = usesAmplification ? .type2DArray : .type2D
        }
        depth.arrayLength = layers
        depth.pixelFormat = Self.depthFormat
        depth.width = width
        depth.height = height
        depth.usage = .renderTarget
        depth.storageMode = transientStorage
        guard let depthTexture = device.makeTexture(descriptor: depth) else { throw RendererError.resource("depth buffers") }

        let targets = EyeTargets(width: width, height: height, color: colorTexture, multisampleColor: multisampleColor, depth: depthTexture)
        eyeTargets = targets
        return targets
    }

    // MARK: - Eye pass

    func encodeEyePass(_ frame: VREyeFrame, targets: EyeTargets, into commandBuffer: MTLCommandBuffer) {
        if usesAmplification {
            let pass = eyePassDescriptor(targets: targets, eye: nil)
            guard let encoder = commandBuffer.makeRenderCommandEncoder(descriptor: pass) else { return }
            encoder.label = "eyes"
            var mappings = [
                MTLVertexAmplificationViewMapping(viewportArrayIndexOffset: 0, renderTargetArrayIndexOffset: 0),
                MTLVertexAmplificationViewMapping(viewportArrayIndexOffset: 0, renderTargetArrayIndexOffset: 1),
            ]
            encoder.setVertexAmplificationCount(2, viewMappings: &mappings)
            drawEyes(frame, targets: targets, encoder: encoder)
            encoder.endEncoding()
        } else {
            for eye in 0..<2 {
                let pass = eyePassDescriptor(targets: targets, eye: eye)
                guard let encoder = commandBuffer.makeRenderCommandEncoder(descriptor: pass) else { return }
                encoder.label = eye == 0 ? "left eye" : "right eye"
                var index = UInt32(eye)
                encoder.setVertexBytes(&index, length: MemoryLayout<UInt32>.stride, index: 4)
                drawEyes(frame, targets: targets, encoder: encoder)
                encoder.endEncoding()
            }
        }
    }

    private func eyePassDescriptor(targets: EyeTargets, eye: Int?) -> MTLRenderPassDescriptor {
        let pass = MTLRenderPassDescriptor()
        let color = pass.colorAttachments[0]
        if let msaa = targets.multisampleColor {
            color?.texture = msaa
            color?.resolveTexture = targets.color
            color?.storeAction = .multisampleResolve
            if let eye { color?.resolveSlice = eye }
        } else {
            color?.texture = targets.color
            color?.storeAction = .store
            if let eye { color?.slice = eye }
        }
        color?.loadAction = .clear
        color?.clearColor = MTLClearColor(red: 0, green: 0, blue: 0, alpha: 1)
        pass.depthAttachment.texture = targets.depth
        pass.depthAttachment.loadAction = .clear
        pass.depthAttachment.clearDepth = 0
        pass.depthAttachment.storeAction = .dontCare
        if eye == nil { pass.renderTargetArrayLength = 2 }
        return pass
    }

    private func drawEyes(_ frame: VREyeFrame, targets: EyeTargets, encoder: MTLRenderCommandEncoder) {
        encoder.setViewport(MTLViewport(originX: 0, originY: 0, width: Double(targets.width), height: Double(targets.height), znear: 0, zfar: 1))
        encoder.setFrontFacing(.counterClockwise)
        let eyes = frame.eyes
        encoder.setVertexBytes(eyes, length: MemoryLayout<VREyeUniforms>.stride * eyes.count, index: 1)
        var shared = frame.frame
        encoder.setVertexBytes(&shared, length: MemoryLayout<VRFrameUniforms>.stride, index: 3)
        encoder.setFragmentBytes(&shared, length: MemoryLayout<VRFrameUniforms>.stride, index: 3)

        // Pixels outside the lens field never reach the panel; covering them at
        // the near plane first lets early depth testing skip their shading.
        encoder.setRenderPipelineState(maskPipeline)
        encoder.setDepthStencilState(maskDepth)
        encoder.setCullMode(.none)
        encoder.setVertexBuffer(maskDirections, offset: 0, index: 0)
        encoder.drawPrimitives(type: .triangleStrip, vertexStart: 0, vertexCount: maskVertexCount)

        encoder.setRenderPipelineState(scenePipeline)
        encoder.setDepthStencilState(opaqueDepth)
        for instance in frame.instances {
            guard let mesh = meshes[instance.mesh] else { continue }
            encoder.setCullMode(instance.mesh == .disc ? .none : .back)
            var uniforms = instance.uniforms
            encoder.setVertexBytes(&uniforms, length: MemoryLayout<VRInstanceUniforms>.stride, index: 2)
            encoder.setFragmentBytes(&uniforms, length: MemoryLayout<VRInstanceUniforms>.stride, index: 2)
            encoder.setVertexBuffer(mesh.vertices, offset: 0, index: 0)
            encoder.drawIndexedPrimitives(type: .triangle, indexCount: mesh.indexCount, indexType: .uint16, indexBuffer: mesh.indices, indexBufferOffset: 0)
        }

        if var voxelUniforms = frame.voxelUniforms, !frame.voxelChunks.isEmpty {
            encoder.setCullMode(.back)
            encoder.setVertexBytes(&voxelUniforms, length: MemoryLayout<VRInstanceUniforms>.stride, index: 2)
            encoder.setFragmentBytes(&voxelUniforms, length: MemoryLayout<VRInstanceUniforms>.stride, index: 2)
            for chunk in frame.voxelChunks where chunk.indexCount >= 3 {
                encoder.setVertexBuffer(chunk.vertices, offset: 0, index: 0)
                encoder.drawIndexedPrimitives(
                    type: .triangle,
                    indexCount: chunk.indexCount,
                    indexType: .uint32,
                    indexBuffer: chunk.indices,
                    indexBufferOffset: 0
                )
            }
        }

        if frame.drawSky {
            encoder.setRenderPipelineState(skyPipeline)
            encoder.setDepthStencilState(skyDepth)
            encoder.setCullMode(.none)
            encoder.drawPrimitives(type: .triangle, vertexStart: 0, vertexCount: 3)
        }

        // The camera image blends over everything farther than its plane, so
        // fading it in cross-fades the room over the scene's background while
        // nearer objects stay in front.
        if let camera = frame.passthrough {
            encoder.setRenderPipelineState(passthroughPipeline)
            encoder.setDepthStencilState(readOnlyDepth)
            encoder.setCullMode(.none)
            var uniforms = camera.uniforms
            encoder.setVertexBytes(&uniforms, length: MemoryLayout<VRPassthroughUniforms>.stride, index: 2)
            encoder.setFragmentBytes(&uniforms, length: MemoryLayout<VRPassthroughUniforms>.stride, index: 2)
            encoder.setFragmentTexture(camera.luma, index: 0)
            encoder.setFragmentTexture(camera.chroma, index: 1)
            encoder.drawPrimitives(type: .triangleStrip, vertexStart: 0, vertexCount: 4)
        }

        if let boundary = frame.boundary, let mesh = meshes[.boundary] {
            encoder.setRenderPipelineState(boundaryPipeline)
            encoder.setDepthStencilState(readOnlyDepth)
            encoder.setCullMode(.none)
            var uniforms = boundary
            encoder.setVertexBytes(&uniforms, length: MemoryLayout<VRInstanceUniforms>.stride, index: 2)
            encoder.setFragmentBytes(&uniforms, length: MemoryLayout<VRInstanceUniforms>.stride, index: 2)
            encoder.setVertexBuffer(mesh.vertices, offset: 0, index: 0)
            encoder.drawIndexedPrimitives(type: .triangle, indexCount: mesh.indexCount, indexType: .uint16, indexBuffer: mesh.indices, indexBufferOffset: 0)
        }

        if !frame.panels.isEmpty {
            encoder.setRenderPipelineState(panelPipeline)
            encoder.setDepthStencilState(overlayDepth)
            encoder.setCullMode(.none)
            for panel in frame.panels {
                var uniforms = panel.uniforms
                encoder.setVertexBytes(&uniforms, length: MemoryLayout<VRPanelUniforms>.stride, index: 2)
                encoder.setFragmentBytes(&uniforms, length: MemoryLayout<VRPanelUniforms>.stride, index: 2)
                encoder.setFragmentTexture(panel.texture, index: 0)
                encoder.drawPrimitives(type: .triangleStrip, vertexStart: 0, vertexCount: 4)
            }
        }

        if var reticle = frame.reticle {
            encoder.setRenderPipelineState(reticlePipeline)
            encoder.setDepthStencilState(overlayDepth)
            encoder.setCullMode(.none)
            encoder.setVertexBytes(&reticle, length: MemoryLayout<VRPanelUniforms>.stride, index: 2)
            encoder.setFragmentBytes(&reticle, length: MemoryLayout<VRPanelUniforms>.stride, index: 2)
            encoder.drawPrimitives(type: .triangleStrip, vertexStart: 0, vertexCount: 4)
        }
    }

    // MARK: - Final pass

    /// Builds the per-eye discs the final pass draws: each lens field's circle
    /// on the panel, slightly oversized for the feathered edge.
    private func discMeshes(for layout: VRStereoLayout) throws -> DiscMeshes {
        let left = layout[.left]
        let key = SIMD4(left.lensCenterPixels.x, left.lensCenterPixels.y, left.visibleRadiusPixels, layout[.right].lensCenterPixels.x)
        if let discs, discs.key == key { return discs }
        var vertices: [SIMD2<Float>] = []
        for eye in VREye.allCases {
            let e = layout[eye]
            let radius = e.visibleRadiusPixels + 3
            for i in 0..<Self.discSegments {
                let a0 = Float(i) / Float(Self.discSegments) * 2 * .pi
                let a1 = Float(i + 1) / Float(Self.discSegments) * 2 * .pi
                // Outscribe the circle so the polygon's flat edges don't clip it.
                let r = radius / cos(.pi / Float(Self.discSegments))
                vertices.append(e.lensCenterPixels)
                vertices.append(e.lensCenterPixels + SIMD2(cos(a0), sin(a0)) * r)
                vertices.append(e.lensCenterPixels + SIMD2(cos(a1), sin(a1)) * r)
            }
        }
        guard let buffer = device.makeBuffer(bytes: vertices, length: vertices.count * MemoryLayout<SIMD2<Float>>.stride, options: .storageModeShared) else {
            throw RendererError.resource("lens discs")
        }
        let meshes = DiscMeshes(buffer: buffer, verticesPerEye: Self.discSegments * 3, key: key)
        discs = meshes
        return meshes
    }

    func encodeFinalPass(_ frame: VRFinalFrame, layout: VRStereoLayout, eyeTexture: MTLTexture, target: MTLTexture, into commandBuffer: MTLCommandBuffer) {
        let pass = MTLRenderPassDescriptor()
        pass.colorAttachments[0].texture = target
        pass.colorAttachments[0].loadAction = .clear
        pass.colorAttachments[0].clearColor = MTLClearColor(red: 0, green: 0, blue: 0, alpha: 1)
        pass.colorAttachments[0].storeAction = .store
        guard let discs = try? discMeshes(for: layout),
              let encoder = commandBuffer.makeRenderCommandEncoder(descriptor: pass) else { return }
        encoder.label = "lens correction"
        encoder.setRenderPipelineState(finalPipeline)
        encoder.setCullMode(.none)
        var shared = frame.frame
        encoder.setVertexBytes(&shared, length: MemoryLayout<VRDistortionFrameUniforms>.stride, index: 1)
        encoder.setFragmentBytes(&shared, length: MemoryLayout<VRDistortionFrameUniforms>.stride, index: 1)
        encoder.setFragmentTexture(eyeTexture, index: 0)
        let stride = MemoryLayout<SIMD2<Float>>.stride * discs.verticesPerEye
        for eye in 0..<min(2, frame.eyes.count) {
            var uniforms = frame.eyes[eye]
            encoder.setFragmentBytes(&uniforms, length: MemoryLayout<VRDistortionEyeUniforms>.stride, index: 2)
            encoder.setVertexBuffer(discs.buffer, offset: eye * stride, index: 0)
            encoder.drawPrimitives(type: .triangle, vertexStart: 0, vertexCount: discs.verticesPerEye)
        }
        encoder.endEncoding()
    }
}

/// Wraps ARKit's camera pixel buffers as Metal textures without copying.
final class VRCameraTextureCache: @unchecked Sendable {
    /// Keeps the Core Video textures alive until the GPU has read them.
    final class Frame: @unchecked Sendable {
        let luma: MTLTexture
        let chroma: MTLTexture
        private let retained: [CVMetalTexture]

        init(luma: MTLTexture, chroma: MTLTexture, retained: [CVMetalTexture]) {
            self.luma = luma
            self.chroma = chroma
            self.retained = retained
        }
    }

    private var cache: CVMetalTextureCache?

    init(device: MTLDevice) {
        var created: CVMetalTextureCache?
        CVMetalTextureCacheCreate(kCFAllocatorDefault, nil, device, nil, &created)
        cache = created
    }

    func textures(for pixelBuffer: CVPixelBuffer) -> Frame? {
        guard let cache, CVPixelBufferGetPlaneCount(pixelBuffer) >= 2 else { return nil }
        func plane(_ index: Int, _ format: MTLPixelFormat) -> (MTLTexture, CVMetalTexture)? {
            let width = CVPixelBufferGetWidthOfPlane(pixelBuffer, index)
            let height = CVPixelBufferGetHeightOfPlane(pixelBuffer, index)
            var cvTexture: CVMetalTexture?
            let status = CVMetalTextureCacheCreateTextureFromImage(kCFAllocatorDefault, cache, pixelBuffer, nil, format, width, height, index, &cvTexture)
            guard status == kCVReturnSuccess, let cvTexture, let texture = CVMetalTextureGetTexture(cvTexture) else { return nil }
            return (texture, cvTexture)
        }
        guard let y = plane(0, .r8Unorm), let cbcr = plane(1, .rg8Unorm) else { return nil }
        return Frame(luma: y.0, chroma: cbcr.0, retained: [y.1, cbcr.1])
    }

    func flush() {
        if let cache { CVMetalTextureCacheFlush(cache, 0) }
    }
}
