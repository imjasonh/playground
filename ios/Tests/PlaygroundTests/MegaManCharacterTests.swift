import XCTest
@testable import Playground

final class MegaManCharacterTests: XCTestCase {
    func testOnlyMetalMan() {
        XCTAssertEqual(MegaManCharacter.all.map(\.id), ["metal-man"])
        XCTAssertEqual(MegaManCharacter.default.id, "metal-man")
        XCTAssertEqual(MegaManCharacter.metalMan.name, "Metal Man")
        XCTAssertEqual(MegaManCharacter.metalMan.frameCount, 16)
    }

    func testFrameAssetNamesWrap() {
        let metal = MegaManCharacter.metalMan
        XCTAssertEqual(metal.frameAssetName(0), "metal-man_00")
        XCTAssertEqual(metal.frameAssetName(15), "metal-man_15")
        XCTAssertEqual(metal.frameAssetName(16), "metal-man_00")
        XCTAssertEqual(metal.frameAssetName(-1), "metal-man_15")
    }
}
