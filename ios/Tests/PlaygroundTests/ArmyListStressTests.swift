import XCTest
@testable import Playground

/// Re-validates the 50 stress-test army list fixtures through the Swift validator.
final class ArmyListStressTests: XCTestCase {
    func testFiftyStressFixturesMatchExpectation() throws {
        let fixtures = try Self.loadFixtures()
        XCTAssertEqual(fixtures.count, 50, "Expected 50 stress fixtures")

        let catalog = try ArmyListCatalogTests.loadCatalogFromRepo()
        var mismatches: [String] = []

        for fixture in fixtures {
            let result = ArmyListValidator.validate(list: fixture.list, catalog: catalog)
            if result.isLegal != fixture.expectedLegal {
                let codes = result.errors.map(\.code).joined(separator: ",")
                mismatches.append(
                    "\(fixture.file): expectedLegal=\(fixture.expectedLegal) gotLegal=\(result.isLegal) errors=\(codes)"
                )
            }
        }

        XCTAssertTrue(mismatches.isEmpty, mismatches.joined(separator: "\n"))
    }

    func testEmptyLeaderToCannotAttach() throws {
        let catalog = try ArmyListCatalogTests.loadCatalogFromRepo()
        let body = ListUnitInstance(datasheetID: "chaos-space-marines--legionaries", models: 10)
        let character = ListUnitInstance(
            datasheetID: "chaos-space-marines--master-of-executions",
            models: 1,
            attachedToUnitID: body.id
        )
        let detachment = try XCTUnwrap(
            catalog.detachments.first {
                $0.factionID == "chaos-space-marines" && $0.detachmentPoints == 2
            }
        )
        let list = ArmyListDocument(
            name: "Empty leaderTo attach",
            catalogVersion: catalog.version,
            factionID: "chaos-space-marines",
            battleSizeID: "incursion",
            detachmentIDs: [detachment.id],
            units: [body, character],
            warlordUnitID: character.id
        )
        let result = ArmyListValidator.validate(list: list, catalog: catalog)
        XCTAssertTrue(result.errors.contains { $0.code == "unit.attachNoTargets" })
    }

    private struct Fixture {
        var file: String
        var expectedLegal: Bool
        var list: ArmyListDocument
    }

    private static func loadFixtures() throws -> [Fixture] {
        let thisFile = URL(fileURLWithPath: #filePath)
        let iosRoot = thisFile
            .deletingLastPathComponent()
            .deletingLastPathComponent()
            .deletingLastPathComponent()
        let dir = iosRoot.appendingPathComponent("Tests/PlaygroundTests/Fixtures/ArmyLists")
        let urls = try FileManager.default.contentsOfDirectory(
            at: dir,
            includingPropertiesForKeys: nil,
            options: [.skipsHiddenFiles]
        )
        .filter { $0.pathExtension == "json" && $0.lastPathComponent != "manifest.json" }
        .sorted { $0.lastPathComponent < $1.lastPathComponent }

        let decoder = JSONDecoder()
        decoder.dateDecodingStrategy = .iso8601

        return try urls.map { url in
            let data = try Data(contentsOf: url)
            let envelope = try decoder.decode(FixtureEnvelope.self, from: data)
            return Fixture(
                file: url.lastPathComponent,
                expectedLegal: envelope.expectedLegal,
                list: envelope.list
            )
        }
    }

    private struct FixtureEnvelope: Decodable {
        var expectedLegal: Bool
        var list: ArmyListDocument
    }
}
