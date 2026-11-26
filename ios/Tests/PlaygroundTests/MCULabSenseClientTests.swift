import XCTest
@testable import Playground

final class MCULabSenseClientTests: XCTestCase {
    func testXiaoESP32S3SenseBoardMetadataAndCompatibility() {
        let board = MCULabBoard.xiaoESP32S3Sense
        XCTAssertEqual(board.rawValue, "xiao-esp32s3-sense")
        XCTAssertEqual(board.boardID, 3)
        XCTAssertEqual(board.chip, "esp32s3")
        XCTAssertEqual(board.chipID, 0x0009)
        XCTAssertEqual(board.gapName, "XIAO-S3")
        XCTAssertTrue(board.compatibleApps.contains(.base))
        XCTAssertTrue(board.compatibleApps.contains(.recorder))
        XCTAssertFalse(board.compatibleApps.contains(.maze))

        let target = MCULabFirmwareTarget(board: .xiaoESP32S3Sense, app: .recorder)
        XCTAssertEqual(target.binName, "xiao-esp32s3-sense-recorder")
        XCTAssertEqual(target.ghcrRepo, "imjasonh/playground/xiao-esp32s3-sense-recorder")

        let metrics = MCULabMetrics(
            seq: 1,
            flags: board.boardID << 4,
            wakeCount: 1,
            sensorUs: 0,
            computeUs: 0,
            epdRefreshUs: 0,
            radioUs: 100_000,
            batteryMv: 5_000
        )
        XCTAssertEqual(metrics.inferredBoard, .xiaoESP32S3Sense)
    }

    func testServerAddressNormalization() {
        XCTAssertEqual(
            MCULabSenseServerAddress.normalize("192.168.4.1")?.absoluteString,
            "http://192.168.4.1"
        )
        XCTAssertEqual(
            MCULabSenseServerAddress.normalize("  http://192.168.1.42:8080/  ")?.absoluteString,
            "http://192.168.1.42:8080"
        )
        XCTAssertNil(MCULabSenseServerAddress.normalize("   "))
        XCTAssertNil(MCULabSenseServerAddress.normalize("ftp://192.168.4.1"))
    }

    func testFormattingHelpers() {
        XCTAssertEqual(MCULabSenseFormatting.formatBytes(512), "512 B")
        XCTAssertEqual(MCULabSenseFormatting.formatBytes(12 * 1024), "12 KB")
        XCTAssertEqual(MCULabSenseFormatting.formatBytes(8 * 1024 * 1024), "8.0 MB")
        XCTAssertEqual(MCULabSenseFormatting.formatBytes(32 * 1024 * 1024 * 1024), "32.0 GB")
        XCTAssertEqual(MCULabSenseFormatting.formatDuration(60), "1:00")
        XCTAssertEqual(MCULabSenseFormatting.formatDuration(125), "2:05")
    }

    func testClientFetchesStatusClipsControlsAndDeletes() async throws {
        let baseURL = try XCTUnwrap(MCULabSenseServerAddress.normalize("192.168.4.1"))
        let fakeHTTP = FakeSenseHTTP()
        fakeHTTP.handler = { req in
            let path = req.url?.path ?? ""
            let method = req.httpMethod ?? "GET"
            switch (method, path) {
            case ("GET", "/api/status"):
                let body = """
                {"board":"xiao-esp32s3-sense","app":"recorder","firmware_id":"xiao-esp32s3-sense-recorder/0.1","recording":true,"clip_duration_s":60,"clip_count":2,"active_clip":"clip_000003.tmp","sd_mounted":true,"sd_total_bytes":32000000000,"sd_free_bytes":31500000000,"wifi_mode":"ap","ssid":"XIAO-S3-Sense","ip":"192.168.4.1","camera_ready":true,"mic_ready":true}
                """
                return try Self.httpResponse(url: req.url!, status: 200, body: body)
            case ("GET", "/api/clips"):
                let body = """
                {"clips":[{"name":"clip_000002.mov","seq":2,"size_bytes":8400000,"duration_s":60},{"name":"clip_000001.mov","seq":1,"size_bytes":7900000,"duration_s":60}],"sd_total_bytes":32000000000,"sd_free_bytes":31500000000,"recording":true}
                """
                return try Self.httpResponse(url: req.url!, status: 200, body: body)
            case ("POST", "/api/record/stop"):
                let body = """
                {"board":"xiao-esp32s3-sense","app":"recorder","firmware_id":"xiao-esp32s3-sense-recorder/0.1","recording":false,"clip_duration_s":60,"clip_count":2,"active_clip":null,"sd_mounted":true,"sd_total_bytes":32000000000,"sd_free_bytes":31500000000,"wifi_mode":"ap","ssid":"XIAO-S3-Sense","ip":"192.168.4.1","camera_ready":true,"mic_ready":true}
                """
                return try Self.httpResponse(url: req.url!, status: 200, body: body)
            case ("DELETE", "/api/clips/clip_000001.mov"):
                return try Self.httpResponse(url: req.url!, status: 200, body: #"{"deleted":"clip_000001.mov"}"#)
            default:
                return try Self.httpResponse(url: req.url!, status: 404, body: #"{"error":"not found"}"#)
            }
        }

        let client = MCULabSenseClient(baseURL: baseURL, http: fakeHTTP)

        let status = try await client.fetchStatus()
        XCTAssertEqual(status.board, "xiao-esp32s3-sense")
        XCTAssertTrue(status.recording)
        XCTAssertEqual(status.clipCount, 2)
        XCTAssertEqual(status.ssid, "XIAO-S3-Sense")

        let clipsResp = try await client.fetchClips()
        XCTAssertEqual(clipsResp.clips.count, 2)
        XCTAssertEqual(clipsResp.clips[0].name, "clip_000002.mov")
        XCTAssertEqual(
            client.clipStreamURL(for: clipsResp.clips[0]).absoluteString,
            "http://192.168.4.1/clips/clip_000002.mov"
        )

        let stopped = try await client.setRecording(false)
        XCTAssertFalse(stopped.recording)
        XCTAssertNil(stopped.activeClip)

        try await client.deleteClip(clipsResp.clips[1])
    }

    func testClientSurfacesHTTPStatusErrors() async throws {
        let baseURL = try XCTUnwrap(MCULabSenseServerAddress.normalize("192.168.4.1"))
        let fakeHTTP = FakeSenseHTTP()
        fakeHTTP.handler = { req in
            try Self.httpResponse(url: req.url!, status: 503, body: "unavailable")
        }
        let client = MCULabSenseClient(baseURL: baseURL, http: fakeHTTP)
        do {
            _ = try await client.fetchStatus()
            XCTFail("Expected httpStatus(503)")
        } catch let error as MCULabSenseClientError {
            XCTAssertEqual(error, .httpStatus(503))
        }
    }

    private static func httpResponse(url: URL, status: Int, body: String) throws -> (Data, URLResponse) {
        let resp = try XCTUnwrap(HTTPURLResponse(
            url: url,
            statusCode: status,
            httpVersion: "HTTP/1.1",
            headerFields: ["Content-Type": "application/json"]
        ))
        return (Data(body.utf8), resp)
    }
}

private final class FakeSenseHTTP: MCULabSenseHTTPClient, @unchecked Sendable {
    var handler: @Sendable (URLRequest) throws -> (Data, URLResponse) = { _ in
        throw URLError(.badServerResponse)
    }

    func data(for request: URLRequest) async throws -> (Data, URLResponse) {
        try handler(request)
    }
}
