import XCTest
@testable import Playground

final class MegaManCharacterTests: XCTestCase {
    func testCatalogHasMegaManAndBosses() {
        let ids = Set(MegaManCharacter.all.map(\.id))
        XCTAssertTrue(ids.contains("mega-man"))
        XCTAssertTrue(ids.contains("metal-man"))
        XCTAssertTrue(ids.contains("wood-man"))
        XCTAssertEqual(MegaManCharacter.all.count, 9)
        XCTAssertEqual(MegaManCharacter.default.id, "metal-man")
    }

    func testFrameAssetNamesWrap() {
        let metal = MegaManCharacter.default
        XCTAssertEqual(metal.frameAssetName(0), "metal-man_00")
        XCTAssertEqual(metal.frameAssetName(7), "metal-man_07")
        XCTAssertEqual(metal.frameAssetName(8), "metal-man_00")
        XCTAssertEqual(metal.frameAssetName(-1), "metal-man_07")
    }

    func testNamedFallsBackToDefault() {
        XCTAssertEqual(MegaManCharacter.named("metal-man").name, "Metal Man")
        XCTAssertEqual(MegaManCharacter.named("nope").id, MegaManCharacter.default.id)
    }

    func testEveryCharacterHasStableFrameCount() {
        for character in MegaManCharacter.all {
            XCTAssertEqual(character.frameCount, 8, character.id)
            XCTAssertFalse(character.name.isEmpty, character.id)
        }
    }
}
