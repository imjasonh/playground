import XCTest
import MapKit
@testable import Playground

final class RideMapPriorityTests: XCTestCase {
    func testCrashIsAlwaysRequired() {
        XCTAssertEqual(
            EventAnnotation.displayPriority(severity: .crash, peakG: 4.2).rawValue,
            MKFeatureDisplayPriority.required.rawValue
        )
    }

    func testHigherGOutranksLowerG() {
        let softPothole = EventAnnotation.displayPriority(severity: .pothole, peakG: 1.6)
        let hardPothole = EventAnnotation.displayPriority(severity: .pothole, peakG: 2.8)
        let impact = EventAnnotation.displayPriority(severity: .impact, peakG: 3.9)
        XCTAssertLessThan(softPothole.rawValue, hardPothole.rawValue)
        XCTAssertLessThan(hardPothole.rawValue, impact.rawValue)
    }

    func testNonCrashNeverReachesRequired() {
        // Even an absurd peak must stay below .required so crash pins always win.
        let extreme = EventAnnotation.displayPriority(severity: .impact, peakG: 50)
        XCTAssertLessThan(extreme.rawValue, MKFeatureDisplayPriority.required.rawValue)
    }

    func testAnnotationCarriesItsOwnPriority() {
        let annotation = EventAnnotation(severity: .impact, peakG: 3.9)
        XCTAssertEqual(
            annotation.displayPriority.rawValue,
            EventAnnotation.displayPriority(severity: .impact, peakG: 3.9).rawValue
        )
    }
}
