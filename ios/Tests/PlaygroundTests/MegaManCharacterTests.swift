import XCTest
@testable import Playground

final class MegaManCharacterTests: XCTestCase {
    func testCatalogHasMegaManAndBosses() {
        let ids = Set(MegaManCharacter.all.map(\.id))
        XCTAssertTrue(ids.contains("mega-man"))
        XCTAssertTrue(ids.contains("metal-man"))
        XCTAssertTrue(ids.contains("wood-man"))
        XCTAssertEqual(MegaManCharacter.all.count, 9)
    }

    func testFrameAssetNamesWrap() {
        let mega = MegaManCharacter.default
        XCTAssertEqual(mega.frameAssetName(0), "mega-man_00")
        XCTAssertEqual(mega.frameAssetName(7), "mega-man_07")
        XCTAssertEqual(mega.frameAssetName(8), "mega-man_00")
        XCTAssertEqual(mega.frameAssetName(-1), "mega-man_07")
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
