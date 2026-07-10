import XCTest
@testable import Playground

final class MegaManCharacterTests: XCTestCase {
    func testOnlyMetalMan() {
        XCTAssertEqual(MegaManCharacter.all.map(\.id), ["metal-man"])
        XCTAssertEqual(MegaManCharacter.default.id, "metal-man")
        XCTAssertEqual(MegaManCharacter.metalMan.name, "Metal Man")
        XCTAssertEqual(MegaManCharacter.metalMan.frameCount, 8)
    }

    func testFrameAssetNamesWrap() {
        let metal = MegaManCharacter.metalMan
        XCTAssertEqual(metal.frameAssetName(0), "metal-man_00")
        XCTAssertEqual(metal.frameAssetName(7), "metal-man_07")
        XCTAssertEqual(metal.frameAssetName(8), "metal-man_00")
        XCTAssertEqual(metal.frameAssetName(-1), "metal-man_07")
    }
}
