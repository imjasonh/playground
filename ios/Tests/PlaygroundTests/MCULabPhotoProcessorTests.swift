import CoreGraphics
import XCTest
@testable import Playground

final class MCULabPhotoProcessorTests: XCTestCase {
    func testBeginDataCommandRoundTrip() {
        let sha = String(repeating: "a", count: 64)
        let raw = MCULabOTACommand.beginData(size: 96_020, sha256: sha, compression: .none)
        XCTAssertEqual(MCULabProtocol.encodeOTACommand(raw), "BEGIN_DATA 96020 \(sha)")
        XCTAssertEqual(MCULabProtocol.parseOTACommand(MCULabProtocol.encodeOTACommand(raw)), raw)

        let deflated = MCULabOTACommand.beginData(size: 288_020, sha256: sha, compression: .deflate)
        XCTAssertEqual(MCULabProtocol.encodeOTACommand(deflated), "BEGIN_DATA 288020 \(sha) deflate")
        XCTAssertEqual(
            MCULabProtocol.parseOTACommand(MCULabProtocol.encodeOTACommand(deflated)),
            deflated
        )
    }

    func testPhotoAppOnlyCompatibleWithWaveshareEPD75() {
        XCTAssertTrue(MCULabBoard.waveshareEPD75.compatibleApps.contains(.photo))
        XCTAssertFalse(MCULabBoard.xiaoESP32C3.compatibleApps.contains(.photo))
        let target = MCULabFirmwareTarget(board: .waveshareEPD75, app: .photo)
        XCTAssertEqual(target.binName, "waveshare-epd75-photo")
    }

    func testPackGray4PlanesMatchesFirmwareUC8179Polarity() {
        var levels = [UInt8](repeating: 3, count: MCULabPhotoProcessor.pixelCount)
        // First 8 pixels: [0, 1, 2, 3, 0, 1, 2, 3]
        // Expected DTM1: 1, 0, 1, 0, 1, 0, 1, 0 = 0xAA
        // Expected DTM2: 1, 1, 0, 0, 1, 1, 0, 0 = 0xCC
        let pattern: [UInt8] = [0, 1, 2, 3, 0, 1, 2, 3]
        for i in 0..<8 {
            levels[i] = pattern[i]
        }
        let packed = MCULabPhotoProcessor.packGray4Planes(levels: levels)
        XCTAssertEqual(packed.count, MCULabPhotoProcessor.gray4FrameBytes)
        XCTAssertEqual(packed[0], 0xAA)
        XCTAssertEqual(packed[MCULabPhotoProcessor.bwFrameBytes], 0xCC)
        // Remaining pixels are white (level 3 -> DTM1=0, DTM2=0).
        XCTAssertEqual(packed[1], 0x00)
        XCTAssertEqual(packed[MCULabPhotoProcessor.bwFrameBytes + 1], 0x00)
    }

    func testPackBW1BitIsMSBFirstOneIsWhite() {
        var levels = [UInt8](repeating: 0, count: MCULabPhotoProcessor.pixelCount)
        levels[0] = 3 // white -> bit 7 = 1
        levels[2] = 3 // white -> bit 5 = 1
        levels[7] = 3 // white -> bit 0 = 1
        let packed = MCULabPhotoProcessor.packBW1Bit(levels: levels)
        XCTAssertEqual(packed.count, MCULabPhotoProcessor.bwFrameBytes)
        XCTAssertEqual(packed[0], 0b1010_0001)
        XCTAssertEqual(packed[1], 0x00)
    }

    func testAlbumEncodeAndParseHeaderRoundTrip() throws {
        let frame0 = Data(repeating: 0xAA, count: MCULabPhotoProcessor.gray4FrameBytes)
        let frame1 = Data(repeating: 0x55, count: MCULabPhotoProcessor.gray4FrameBytes)
        let album = try XCTUnwrap(
            MCULabPhotoProcessor.encodeAlbum(
                mode: .gray4,
                intervalSecs: 600,
                frames: [frame0, frame1]
            )
        )
        XCTAssertEqual(
            album.count,
            MCULabPhotoProcessor.headerLength + 2 * MCULabPhotoProcessor.gray4FrameBytes
        )
        let header = try XCTUnwrap(MCULabPhotoProcessor.parseAlbumHeader(album))
        XCTAssertEqual(header.mode, .gray4)
        XCTAssertEqual(header.count, 2)
        XCTAssertEqual(header.intervalSecs, 600)
        XCTAssertEqual(
            header.payloadCRC32,
            MCULabProtocol.crc32(album.dropFirst(MCULabPhotoProcessor.headerLength))
        )

        // Corrupt a header byte and verify CRC rejection.
        var corrupted = album
        corrupted[8] ^= 0x01
        XCTAssertNil(MCULabPhotoProcessor.parseAlbumHeader(corrupted))

        // Empty album or mismatched frame length rejected.
        XCTAssertNil(MCULabPhotoProcessor.encodeAlbum(mode: .gray4, intervalSecs: 600, frames: []))
        XCTAssertNil(
            MCULabPhotoProcessor.encodeAlbum(
                mode: .gray4,
                intervalSecs: 600,
                frames: [Data(repeating: 0, count: 123)]
            )
        )
    }

    func testProcessGradientImageAcrossModesAndDitherers() throws {
        let gradient = try XCTUnwrap(makeHorizontalGradientCGImage(width: 160, height: 96))

        for algo in MCULabPhotoDitherAlgorithm.allCases {
            var grayOpts = MCULabPhotoOptions()
            grayOpts.mode = .gray4
            grayOpts.dither = algo
            let grayOut = try XCTUnwrap(MCULabPhotoProcessor.process(cgImage: gradient, options: grayOpts))
            XCTAssertEqual(grayOut.frameData.count, MCULabPhotoProcessor.gray4FrameBytes)
            XCTAssertEqual(grayOut.levels.count, MCULabPhotoProcessor.pixelCount)
            let uniqueLevels = Set(grayOut.levels)
            XCTAssertEqual(uniqueLevels, Set([0, 1, 2, 3]), "4-gray gradient should use all 4 levels for \(algo)")

            let preview = try XCTUnwrap(MCULabPhotoProcessor.makePreviewCGImage(levels: grayOut.levels))
            XCTAssertEqual(preview.width, MCULabPhotoProcessor.panelWidth)
            XCTAssertEqual(preview.height, MCULabPhotoProcessor.panelHeight)
        }

        var bwOpts = MCULabPhotoOptions()
        bwOpts.mode = .bw1Bit
        bwOpts.dither = .atkinson
        let bwOut = try XCTUnwrap(MCULabPhotoProcessor.process(cgImage: gradient, options: bwOpts))
        XCTAssertEqual(bwOut.frameData.count, MCULabPhotoProcessor.bwFrameBytes)
        XCTAssertEqual(Set(bwOut.levels), Set([0, 3]))
    }

    @MainActor
    func testArmDataBlobUploadTargetsWaveshareIndependentOfSelectedBoard() throws {
        let suite = "mcu-lab-photo.tests.\(UUID().uuidString)"
        let defaults = try XCTUnwrap(UserDefaults(suiteName: suite))
        defaults.removePersistentDomain(forName: suite)
        defer { defaults.removePersistentDomain(forName: suite) }

        let controller = MCULabController(defaults: defaults)
        controller.selectedBoard = .xiaoESP32C3

        let frame = Data(repeating: 0xFF, count: MCULabPhotoProcessor.bwFrameBytes)
        let album = try XCTUnwrap(
            MCULabPhotoProcessor.encodeAlbum(mode: .bw1Bit, intervalSecs: 0, frames: [frame])
        )
        controller.armDataBlobUpload(data: album, name: "1 photo (1-Bit B&W)", targetBoard: .waveshareEPD75)

        XCTAssertEqual(controller.otaPhase, .armed)
        XCTAssertEqual(controller.otaTransferKind, .dataBlob)
        XCTAssertEqual(controller.activeTransferBoard, .waveshareEPD75)
        XCTAssertEqual(controller.stagedFirmwareData, album)
    }

    private func makeHorizontalGradientCGImage(width: Int, height: Int) -> CGImage? {
        var pixels = [UInt8](repeating: 255, count: width * height * 4)
        for y in 0..<height {
            for x in 0..<width {
                let v = UInt8((x * 255) / max(1, width - 1))
                let idx = (y * width + x) * 4
                pixels[idx] = v
                pixels[idx + 1] = v
                pixels[idx + 2] = v
                pixels[idx + 3] = 255
            }
        }
        let colorSpace = CGColorSpaceCreateDeviceRGB()
        let data = Data(pixels)
        guard let provider = CGDataProvider(data: data as CFData) else { return nil }
        return CGImage(
            width: width,
            height: height,
            bitsPerComponent: 8,
            bitsPerPixel: 32,
            bytesPerRow: width * 4,
            space: colorSpace,
            bitmapInfo: CGBitmapInfo(rawValue: CGImageAlphaInfo.premultipliedLast.rawValue),
            provider: provider,
            decode: nil,
            shouldInterpolate: true,
            intent: .defaultIntent
        )
    }
}
