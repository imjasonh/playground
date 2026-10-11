import Metal
import XCTest
import simd
@testable import Playground

/// Compiles the shaders, checks Swift and Metal agree on buffer layouts, and
/// renders a full frame offscreen to check what lands on the panel.
final class PhoneVRRendererTests: XCTestCase {
    private func metalDevice() throws -> MTLDevice {
        guard let device = MTLCreateSystemDefaultDevice() else { throw XCTSkip("No Metal device on this runner") }
        return device
    }

    func testShadersCompileForBothStereoPaths() throws {
        let device = try metalDevice()
        let library = try VRRenderer.makeLibrary(device: device, amplification: false)
        let functions = [
            "scene_vertex", "scene_fragment", "boundary_fragment", "sky_vertex", "sky_fragment",
            "mask_vertex", "mask_fragment", "panel_vertex", "panel_fragment", "reticle_fragment",
            "passthrough_vertex", "passthrough_fragment", "final_vertex", "final_fragment",
        ]
        for name in functions {
            XCTAssertNotNil(library.makeFunction(name: name), name)
        }
        if VRRenderer.supportsSinglePassStereo(device) {
            let amplified = try VRRenderer.makeLibrary(device: device, amplification: true)
            XCTAssertNotNil(amplified.makeFunction(name: "scene_vertex"))
            _ = try VRRenderer.pipelineDescriptors(library: amplified, amplification: true, sampleCount: 4)
                .values.map { try device.makeRenderPipelineState(descriptor: $0) }
        }
    }

    func testRendererBuildsEveryPipeline() throws {
        let device = try metalDevice()
        var options = VRRenderer.Options()
        options.memorylessTargets = false
        let renderer = try VRRenderer(device: device, options: options)
        let targets = try renderer.ensureEyeTargets(width: 256, height: 256)
        XCTAssertEqual(targets.color.arrayLength, 2)
        XCTAssertEqual(targets.color.textureType, .type2DArray)
    }

    func testBufferLayoutsMatchSwift() throws {
        let device = try metalDevice()
        let library = try VRRenderer.makeLibrary(device: device, amplification: false)
        let descriptors = try VRRenderer.pipelineDescriptors(library: library, amplification: false, sampleCount: 1)
        var sizes: [String: Int] = [:]
        for (name, descriptor) in descriptors {
            let (_, reflection) = try device.makeRenderPipelineState(descriptor: descriptor, options: [.bindingInfo, .bufferTypeInfo])
            guard let reflection else { continue }
            for binding in reflection.vertexBindings + reflection.fragmentBindings where binding.type == .buffer {
                guard let buffer = binding as? MTLBufferBinding else { continue }
                sizes["\(name).\(binding.name)"] = buffer.bufferDataSize
            }
        }
        XCTAssertEqual(sizes["scene.eyes"], MemoryLayout<VREyeUniforms>.stride)
        XCTAssertEqual(sizes["scene.instance"], MemoryLayout<VRInstanceUniforms>.stride)
        XCTAssertEqual(sizes["scene.frame"], MemoryLayout<VRFrameUniforms>.stride)
        XCTAssertEqual(sizes["panel.panel"], MemoryLayout<VRPanelUniforms>.stride)
        XCTAssertEqual(sizes["reticle.panel"], MemoryLayout<VRPanelUniforms>.stride)
        XCTAssertEqual(sizes["passthrough.camera"], MemoryLayout<VRPassthroughUniforms>.stride)
        XCTAssertEqual(sizes["mask.directions"], MemoryLayout<SIMD4<Float>>.stride)
        XCTAssertEqual(sizes["final.pixels"], MemoryLayout<SIMD2<Float>>.stride)
        XCTAssertEqual(sizes["final.eye"], MemoryLayout<VRDistortionEyeUniforms>.stride)
        XCTAssertEqual(sizes["final.frame"], MemoryLayout<VRDistortionFrameUniforms>.stride)
    }

    private struct Rendered {
        let width: Int
        let height: Int
        let bytes: [UInt8]

        /// Red, green, blue, alpha at a drawable pixel.
        func pixel(_ x: Int, _ y: Int) -> SIMD4<Int> {
            let i = (y * width + x) * 4
            return SIMD4(Int(bytes[i + 2]), Int(bytes[i + 1]), Int(bytes[i]), Int(bytes[i + 3]))
        }

        /// Centre of the pixels within `radius` of `center` that pass `matches`.
        func centroid(near center: SIMD2<Float>, radius: Int, _ matches: (SIMD4<Int>) -> Bool) -> SIMD2<Float>? {
            var sum = SIMD2<Float>.zero
            var count: Float = 0
            let cx = Int(center.x)
            let cy = Int(center.y)
            for y in max(0, cy - radius)..<min(height, cy + radius) {
                for x in max(0, cx - radius)..<min(width, cx + radius) where matches(pixel(x, y)) {
                    sum += SIMD2(Float(x), Float(y))
                    count += 1
                }
            }
            return count > 0 ? sum / count : nil
        }
    }

    private func renderMarkers(singlePass: Bool) throws -> (Rendered, VRStereoLayout)? {
        let device = try metalDevice()
        if singlePass, !VRRenderer.supportsSinglePassStereo(device) { return nil }
        var options = VRRenderer.Options()
        options.multisample = false
        options.singlePassStereo = singlePass
        options.memorylessTargets = false
        let renderer = try VRRenderer(device: device, options: options)
        XCTAssertEqual(renderer.usesAmplification, singlePass)

        let screen = VRPhoneScreen.iPhone15Pro
        let layout = VRStereoLayout(screen: screen, profile: .standard)
        let size = layout.eyeBufferSize(resolution: 768)
        let targets = try renderer.ensureEyeTargets(width: size.width, height: size.height)
        let head = VRPose(rotation: VRMath.identityRotation, position: SIMD3(0, 1.6, 0))

        // A white marker straight ahead at half a meter and a red one just above it.
        var instances = VRFrameBuilder.instances(scene: .studio, reduced: false, time: 0, passthrough: false)
        let white = VRSceneObject(mesh: .cube, material: .emissive, position: SIMD3(0, 1.6, -0.5), scale: SIMD3(repeating: 0.03), color: VRPalette.white, glow: 4)
        let red = VRSceneObject(mesh: .cube, material: .emissive, position: SIMD3(0, 1.7, -0.5), scale: SIMD3(repeating: 0.03), color: VRPalette.rgba(0xFF0000), glow: 4)
        instances.append(VRFrameBuilder.instance(white, time: 0))
        instances.append(VRFrameBuilder.instance(red, time: 0))

        let eyeFrame = VREyeFrame(
            eyes: VRFrameBuilder.eyeUniforms(layout: layout, sceneFromHead: head),
            frame: VRFrameBuilder.frameUniforms(boundaryCenter: .zero, boundaryRadius: 1.5, boundaryVisibility: 0),
            instances: instances,
            boundary: nil,
            panels: [],
            reticle: nil,
            passthrough: nil,
            drawSky: true
        )
        let finalFrame = VRFinalFrame(
            eyes: VRFrameBuilder.distortionEyes(layout: layout, timewarp: VRMath.identityRotation, vignette: 1),
            frame: VRFrameBuilder.distortionFrame(layout: layout, chromaticCorrection: true, brightness: 1)
        )

        let outputDescriptor = MTLTextureDescriptor.texture2DDescriptor(
            pixelFormat: VRRenderer.drawableFormat, width: screen.widthPixels, height: screen.heightPixels, mipmapped: false
        )
        outputDescriptor.usage = [.renderTarget, .shaderRead]
        outputDescriptor.storageMode = .private
        let output = try XCTUnwrap(device.makeTexture(descriptor: outputDescriptor))
        let bytesPerRow = screen.widthPixels * 4
        let length = bytesPerRow * screen.heightPixels
        let readback = try XCTUnwrap(device.makeBuffer(length: length, options: .storageModeShared))
        let commands = try XCTUnwrap(renderer.commandQueue.makeCommandBuffer())
        renderer.encodeEyePass(eyeFrame, targets: targets, into: commands)
        renderer.encodeFinalPass(finalFrame, layout: layout, eyeTexture: targets.color, target: output, into: commands)
        let blit = try XCTUnwrap(commands.makeBlitCommandEncoder())
        blit.copy(
            from: output, sourceSlice: 0, sourceLevel: 0,
            sourceOrigin: MTLOrigin(x: 0, y: 0, z: 0),
            sourceSize: MTLSize(width: screen.widthPixels, height: screen.heightPixels, depth: 1),
            to: readback, destinationOffset: 0, destinationBytesPerRow: bytesPerRow, destinationBytesPerImage: length
        )
        blit.endEncoding()
        commands.commit()
        commands.waitUntilCompleted()
        XCTAssertNil(commands.error)
        let bytes = Array(UnsafeBufferPointer(start: readback.contents().assumingMemoryBound(to: UInt8.self), count: length))
        return (Rendered(width: screen.widthPixels, height: screen.heightPixels, bytes: bytes), layout)
    }

    private func checkFrame(_ frame: Rendered, layout: VRStereoLayout) {
        func brightness(_ p: SIMD4<Int>) -> Int { p.x + p.y + p.z }
        // Outside both lens fields the panel stays black.
        XCTAssertEqual(brightness(frame.pixel(4, 4)), 0)
        XCTAssertEqual(brightness(frame.pixel(frame.width / 2, frame.height / 2)), 0)
        XCTAssertEqual(brightness(frame.pixel(frame.width - 4, frame.height - 4)), 0)

        let isWhite: (SIMD4<Int>) -> Bool = { $0.x > 235 && $0.y > 235 && $0.z > 235 }
        let isRed: (SIMD4<Int>) -> Bool = { $0.x > 200 && $0.y < 70 && $0.z < 70 }
        for eye in VREye.allCases {
            let center = layout[eye].lensCenterPixels
            // The scene fills the field: sky above, floor or objects below.
            XCTAssertGreaterThan(brightness(frame.pixel(Int(center.x), Int(center.y) - 280)), 0, "\(eye) sky")
            XCTAssertGreaterThan(brightness(frame.pixel(Int(center.x) + 150, Int(center.y) + 280)), 0, "\(eye) floor")
            guard let white = frame.centroid(near: center, radius: 300, isWhite),
                  let red = frame.centroid(near: center, radius: 300, isRed) else {
                return XCTFail("\(eye): markers not found")
            }
            // Close, centred objects appear inboard in each eye; flipped eyes would invert depth.
            let offset = white.x - center.x
            if eye == .left {
                XCTAssertGreaterThan(offset, 20, "left eye marker offset \(offset)")
            } else {
                XCTAssertLessThan(offset, -20, "right eye marker offset \(offset)")
            }
            // The higher marker is higher on the panel: nothing in the pipeline flips vertically.
            XCTAssertLessThan(red.y, white.y - 60, "\(eye) red \(red) white \(white)")
            XCTAssertEqual(red.x, white.x, accuracy: 8)
        }
    }

    func testOffscreenFrameShowsBothEyesTheRightWayUp() throws {
        guard let rendered = try renderMarkers(singlePass: false) else { return XCTFail("render failed") }
        checkFrame(rendered.0, layout: rendered.1)
    }

    func testSinglePassStereoMatchesTwoPasses() throws {
        guard let amplified = try renderMarkers(singlePass: true) else {
            throw XCTSkip("Vertex amplification isn't supported here")
        }
        let single = amplified.0
        checkFrame(single, layout: amplified.1)
        guard let twoPass = try renderMarkers(singlePass: false) else { return XCTFail("render failed") }
        let double = twoPass.0
        var differing = 0
        for i in stride(from: 0, to: single.bytes.count, by: 4) where abs(Int(single.bytes[i]) - Int(double.bytes[i])) > 8 {
            differing += 1
        }
        XCTAssertLessThan(Double(differing) / Double(single.bytes.count / 4), 0.001)
    }
}
