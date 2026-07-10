import XCTest
import CoreLocation
@testable import Playground

final class HumGeoTests: XCTestCase {
    func testNormalizeAngleWrapsAround() {
        XCTAssertEqual(HumGeo.normalizeAngleDegrees(0), 0, accuracy: 1e-9)
        XCTAssertEqual(HumGeo.normalizeAngleDegrees(190), -170, accuracy: 1e-9)
        XCTAssertEqual(HumGeo.normalizeAngleDegrees(-190), 170, accuracy: 1e-9)
        XCTAssertEqual(HumGeo.normalizeAngleDegrees(360), 0, accuracy: 1e-9)
    }

    func testBearingNorth() {
        let from = CLLocationCoordinate2D(latitude: 40.0, longitude: -74.0)
        let to = CLLocationCoordinate2D(latitude: 40.1, longitude: -74.0)
        XCTAssertEqual(HumGeo.bearingDegrees(from: from, to: to), 0, accuracy: 0.5)
    }

    func testBearingEast() {
        let from = CLLocationCoordinate2D(latitude: 0, longitude: 0)
        let to = CLLocationCoordinate2D(latitude: 0, longitude: 1)
        XCTAssertEqual(HumGeo.bearingDegrees(from: from, to: to), 90, accuracy: 0.5)
    }

    func testDistanceKnownShortLeg() {
        // ~111.2 km per degree latitude near the equator / mid-latitudes approx.
        let from = CLLocationCoordinate2D(latitude: 40.0, longitude: -74.0)
        let to = CLLocationCoordinate2D(latitude: 40.001, longitude: -74.0)
        let meters = HumGeo.distanceMeters(from: from, to: to)
        XCTAssertEqual(meters, 111.2, accuracy: 2.0)
    }

    func testDestinationRoundTrip() {
        let origin = CLLocationCoordinate2D(latitude: 37.7749, longitude: -122.4194)
        let dest = HumGeo.destination(from: origin, bearingDegrees: 45, distanceMeters: 250)
        let backBearing = HumGeo.bearingDegrees(from: origin, to: dest)
        let distance = HumGeo.distanceMeters(from: origin, to: dest)
        XCTAssertEqual(backBearing, 45, accuracy: 0.5)
        XCTAssertEqual(distance, 250, accuracy: 1.0)
    }

    func testRelativeBearing() {
        // Target north, facing east → target is 90° to the left → -90.
        XCTAssertEqual(
            HumGeo.relativeBearingDegrees(targetBearing: 0, heading: 90),
            -90,
            accuracy: 1e-9
        )
        // Target east, facing north → +90 (right).
        XCTAssertEqual(
            HumGeo.relativeBearingDegrees(targetBearing: 90, heading: 0),
            90,
            accuracy: 1e-9
        )
    }

    func testHideSpotUsesInjectedRandomness() {
        let origin = CLLocationCoordinate2D(latitude: 40.7128, longitude: -74.0060)
        let spot = HumGeo.hideSpot(
            from: origin,
            minDistanceMeters: 100,
            maxDistanceMeters: 100,
            randomBearing: { 90 },
            randomUnit: { 0 }
        )
        let distance = HumGeo.distanceMeters(from: origin, to: spot)
        let bearing = HumGeo.bearingDegrees(from: origin, to: spot)
        XCTAssertEqual(distance, 100, accuracy: 1.0)
        XCTAssertEqual(bearing, 90, accuracy: 0.5)
    }
}

final class HumGameTests: XCTestCase {
    private let origin = CLLocationCoordinate2D(latitude: 40.7359, longitude: -73.9911)

    func testStartHuntHidesWithinConfiguredRange() {
        let config = HumHuntConfig(
            minHideDistanceMeters: 150,
            maxHideDistanceMeters: 150,
            findRadiusMeters: 20
        )
        let game = HumGame(config: config)
        XCTAssertTrue(game.startHunt(from: origin, randomBearing: { 0 }, randomUnit: { 0 }))
        XCTAssertEqual(game.phase, .hunting)
        let hidden = try! XCTUnwrap(game.hiddenCoordinate)
        let distance = HumGeo.distanceMeters(from: origin, to: hidden)
        XCTAssertEqual(distance, 150, accuracy: 1.0)
    }

    func testCannotStartSecondHuntWhileHunting() {
        let game = HumGame()
        XCTAssertTrue(game.startHunt(from: origin, randomBearing: { 10 }, randomUnit: { 0.5 }))
        XCTAssertFalse(game.startHunt(from: origin, randomBearing: { 200 }, randomUnit: { 0.1 }))
    }

    func testAudioParamsCenterWhenFacingTarget() {
        let params = HumGame.audioParams(
            relativeBearingDegrees: 0,
            distanceMeters: 50,
            config: HumHuntConfig()
        )
        XCTAssertEqual(params.pan, 0, accuracy: 0.05)
        XCTAssertLessThan(params.muffling, 0.2)
        XCTAssertGreaterThan(params.volume, 0.3)
    }

    func testAudioParamsPanRightWhenTargetIsRight() {
        let params = HumGame.audioParams(
            relativeBearingDegrees: 90,
            distanceMeters: 100,
            config: HumHuntConfig()
        )
        XCTAssertEqual(params.pan, 1, accuracy: 0.05)
    }

    func testAudioParamsQuieterBehind() {
        let ahead = HumGame.audioParams(
            relativeBearingDegrees: 0,
            distanceMeters: 100,
            config: HumHuntConfig()
        )
        let behind = HumGame.audioParams(
            relativeBearingDegrees: 180,
            distanceMeters: 100,
            config: HumHuntConfig()
        )
        XCTAssertGreaterThan(ahead.volume, behind.volume)
        XCTAssertGreaterThan(behind.muffling, ahead.muffling)
    }

    func testCloserRaisesPitchAndVolume() {
        let far = HumGame.audioParams(
            relativeBearingDegrees: 0,
            distanceMeters: 300,
            config: HumHuntConfig()
        )
        let near = HumGame.audioParams(
            relativeBearingDegrees: 0,
            distanceMeters: 30,
            config: HumHuntConfig()
        )
        XCTAssertGreaterThan(near.frequencyHz, far.frequencyHz)
        XCTAssertGreaterThan(near.volume, far.volume)
    }

    func testFindingSpotTransitionsToFound() {
        let config = HumHuntConfig(
            minHideDistanceMeters: 100,
            maxHideDistanceMeters: 100,
            findRadiusMeters: 25
        )
        let game = HumGame(config: config)
        XCTAssertTrue(game.startHunt(from: origin, randomBearing: { 0 }, randomUnit: { 0 }))
        let hidden = try! XCTUnwrap(game.hiddenCoordinate)

        // Still far — stay hunting.
        let mid = game.update(location: origin, headingDegrees: 0)
        XCTAssertEqual(mid.phase, .hunting)

        // Step onto the spot.
        let win = game.update(location: hidden, headingDegrees: 0)
        XCTAssertEqual(win.phase, .found)
        XCTAssertEqual(game.phase, .found)
        XCTAssertTrue(win.statusMessage.lowercased().contains("found"))
    }

    func testStopResetsToIdle() {
        let game = HumGame()
        _ = game.startHunt(from: origin, randomBearing: { 45 }, randomUnit: { 0.2 })
        game.stop()
        XCTAssertEqual(game.phase, .idle)
        XCTAssertNil(game.hiddenCoordinate)
    }
}
