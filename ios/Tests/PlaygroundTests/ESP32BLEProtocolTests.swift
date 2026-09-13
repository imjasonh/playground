import XCTest
@testable import Playground

final class ESP32BLEProtocolTests: XCTestCase {
    func testParseLEDAliases() {
        XCTAssertEqual(ESP32BLEProtocol.parseCommand("led on"), .ledOn)
        XCTAssertEqual(ESP32BLEProtocol.parseCommand("LED ON"), .ledOn)
        XCTAssertEqual(ESP32BLEProtocol.parseCommand("on"), .ledOn)
        XCTAssertEqual(ESP32BLEProtocol.parseCommand("led off"), .ledOff)
        XCTAssertEqual(ESP32BLEProtocol.parseCommand("off"), .ledOff)
        XCTAssertEqual(ESP32BLEProtocol.parseCommand("stop"), .stop)
    }

    func testParseBlinkForms() {
        XCTAssertEqual(ESP32BLEProtocol.parseCommand("blink 1"), .blink(periodMs: 1000))
        XCTAssertEqual(ESP32BLEProtocol.parseCommand("blink 1s"), .blink(periodMs: 1000))
        XCTAssertEqual(ESP32BLEProtocol.parseCommand("blink every 1s"), .blink(periodMs: 1000))
        XCTAssertEqual(ESP32BLEProtocol.parseCommand("blink 0.5"), .blink(periodMs: 500))
        XCTAssertEqual(ESP32BLEProtocol.parseCommand("blink 500ms"), .blink(periodMs: 500))
        XCTAssertEqual(ESP32BLEProtocol.parseCommand("blink 2s"), .blink(periodMs: 2000))
    }

    func testRejectBadCommands() {
        XCTAssertNil(ESP32BLEProtocol.parseCommand(""))
        XCTAssertNil(ESP32BLEProtocol.parseCommand("blink"))
        XCTAssertNil(ESP32BLEProtocol.parseCommand("blink 0"))
        XCTAssertNil(ESP32BLEProtocol.parseCommand("blink 0.01"))
        XCTAssertNil(ESP32BLEProtocol.parseCommand("blink 120s"))
        XCTAssertNil(ESP32BLEProtocol.parseCommand("led"))
        XCTAssertNil(ESP32BLEProtocol.parseCommand("led blink"))
        XCTAssertNil(ESP32BLEProtocol.parseCommand("wave"))
    }

    func testEncodeRoundTrip() {
        let commands: [ESP32BLECommand] = [
            .ledOn,
            .ledOff,
            .stop,
            .blink(periodMs: 1000),
            .blink(periodMs: 500),
            .blink(periodMs: 250),
        ]
        for command in commands {
            let encoded = ESP32BLEProtocol.encode(command)
            XCTAssertEqual(ESP32BLEProtocol.parseCommand(encoded), command, encoded)
        }
    }

    func testStatusRoundTripWithHeap() {
        let status = ESP32BLEStatus(
            ledOn: true,
            blinkMs: 1000,
            uptimeS: 12,
            heapFree: 185_432,
            lastCommand: "led on"
        )
        let line = ESP32BLEProtocol.formatStatus(status)
        XCTAssertEqual(line, "led=on blink_ms=1000 uptime_s=12 heap=185432 last=led on")
        XCTAssertEqual(ESP32BLEProtocol.parseStatus(line), status)
    }

    func testStatusRoundTripWithoutHeap() {
        let status = ESP32BLEStatus(
            ledOn: false,
            blinkMs: 0,
            uptimeS: 3,
            heapFree: nil,
            lastCommand: ""
        )
        let line = ESP32BLEProtocol.formatStatus(status)
        XCTAssertEqual(line, "led=off blink_ms=0 uptime_s=3 last=")
        XCTAssertEqual(ESP32BLEProtocol.parseStatus(line), status)
    }

    func testUUIDLiteralsMatchFirmware() {
        XCTAssertEqual(
            ESP32BLEProtocol.serviceUUIDString.lowercased(),
            "4fafc201-1fb5-459e-8fcc-c5c9c331914b"
        )
        XCTAssertEqual(
            ESP32BLEProtocol.commandUUIDString.lowercased(),
            "beb5483e-36e1-4688-b7f5-ea07361b26a6"
        )
        XCTAssertEqual(
            ESP32BLEProtocol.statusUUIDString.lowercased(),
            "1a3c0001-36e1-4688-b7f5-ea07361b26a6"
        )
        XCTAssertEqual(ESP32BLEProtocol.deviceName, "PlaygroundBLE")
    }
}
