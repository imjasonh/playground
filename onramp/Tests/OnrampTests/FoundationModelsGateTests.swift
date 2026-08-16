import XCTest
@testable import Onramp

final class FoundationModelsStatusTests: XCTestCase {
    func testHardBlockFlags() {
        XCTAssertTrue(FoundationModelsStatus.unsupportedOperatingSystem.isHardBlock)
        XCTAssertTrue(FoundationModelsStatus.deviceNotEligible.isHardBlock)
        XCTAssertTrue(FoundationModelsStatus.unavailableOther("x").isHardBlock)
        XCTAssertFalse(FoundationModelsStatus.needsAppleIntelligenceEnabled.isHardBlock)
        XCTAssertFalse(FoundationModelsStatus.modelNotReady.isHardBlock)
        XCTAssertFalse(FoundationModelsStatus.available.isHardBlock)
    }

    func testSetupRequiredFlags() {
        XCTAssertTrue(FoundationModelsStatus.needsAppleIntelligenceEnabled.isSetupRequired)
        XCTAssertTrue(FoundationModelsStatus.modelNotReady.isSetupRequired)
        XCTAssertFalse(FoundationModelsStatus.unsupportedOperatingSystem.isSetupRequired)
        XCTAssertFalse(FoundationModelsStatus.deviceNotEligible.isSetupRequired)
        XCTAssertFalse(FoundationModelsStatus.available.isSetupRequired)
    }

    func testBlocksMainUI() {
        XCTAssertTrue(FoundationModelsStatus.checking.blocksMainUI)
        XCTAssertTrue(FoundationModelsStatus.modelNotReady.blocksMainUI)
        XCTAssertTrue(FoundationModelsStatus.unsupportedOperatingSystem.blocksMainUI)
        XCTAssertFalse(FoundationModelsStatus.available.blocksMainUI)
    }

    @MainActor
    func testPlaybooksEscapeDoesNotBypassHardBlock() {
        let gate = FoundationModelsGateModel()
        // Force a hard-block-like session flag attempt.
        gate.allowPlaybooksWithoutModel = true
        // evaluate() on this Linux/CI host without macOS 26 FM will be unsupported OS
        // when the framework isn't available — refresh should keep hard block semantics.
        gate.refresh()
        if gate.status.isHardBlock {
            XCTAssertFalse(gate.showsMainApp)
            gate.continueWithPlaybooksOnly()
            // continueWithPlaybooksOnly sets the flag, but showsMainApp still requires !hardBlock
            XCTAssertTrue(gate.allowPlaybooksWithoutModel)
            XCTAssertFalse(gate.showsMainApp)
        }
    }
}
