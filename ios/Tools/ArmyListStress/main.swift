import Foundation

/// macOS CLI: build stress lists, validate with the Swift `ArmyListValidator`,
/// optionally write XCTest fixtures.
@main
enum ArmyListStressMain {
    static func main() throws {
        let args = Array(CommandLine.arguments.dropFirst())
        var writeFixtures = false
        var catalogPath: String?
        var fixturesDir: String?

        var i = 0
        while i < args.count {
            switch args[i] {
            case "--write-fixtures":
                writeFixtures = true
            case "--catalog":
                i += 1
                guard i < args.count else { fatalError("--catalog requires a path") }
                catalogPath = args[i]
            case "--fixtures-dir":
                i += 1
                guard i < args.count else { fatalError("--fixtures-dir requires a path") }
                fixturesDir = args[i]
            case "--help", "-h":
                print(
                    """
                    army-list-stress — build ~50 lists and validate with ArmyListValidator

                    Usage:
                      army-list-stress [--write-fixtures] [--catalog PATH] [--fixtures-dir PATH]

                    Requires macOS + Xcode. The Swift validator is the only legality oracle.
                    """
                )
                return
            default:
                fatalError("Unknown argument: \(args[i])")
            }
            i += 1
        }

        let catalogURL = URL(fileURLWithPath: catalogPath ?? defaultCatalogPath())
        let fixturesURL = URL(fileURLWithPath: fixturesDir ?? defaultFixturesPath())

        let catalog = try CatalogLoader.load(from: catalogURL)
        print("Catalog \(catalog.version): \(catalog.factions.count) factions")

        let lists = ArmyListStressHarness.buildFifty(catalog: catalog)
        print("Built \(lists.count) stress lists")

        var ok = 0
        for built in lists {
            let result = ArmyListValidator.validate(list: built.list, catalog: catalog)
            let status = result.isLegal ? "LEGAL" : "ILLEGAL"
            let expect = built.expectLegal ? "LEGAL" : "ILLEGAL"
            let mark = result.isLegal == built.expectLegal ? "OK" : "BUG?"
            if result.isLegal == built.expectLegal { ok += 1 }
            let errCodes = Set(result.errors.map(\.code)).sorted().joined(separator: ",")
            let codes = errCodes.isEmpty ? "-" : errCodes
            let name = built.name.prefix(60)
            print(
                "  [\(mark)] \(status) (expect \(expect)) \(name) \(result.totalPoints)pts DP=\(result.detachmentPointsSpent) errs=\(codes)"
            )
        }

        let mismatches = ArmyListStressHarness.mismatches(in: lists, catalog: catalog)
        print("\nExpectation matches: \(ok)/\(lists.count)")
        if !mismatches.isEmpty {
            print("Mismatches:")
            for line in mismatches {
                print("  \(line)")
            }
        }

        if writeFixtures {
            try ArmyListStressHarness.writeFixtures(lists, to: fixturesURL)
            print("Wrote \(lists.count) fixtures to \(fixturesURL.path)")
        }

        if !mismatches.isEmpty {
            exit(1)
        }
    }

    private static func defaultCatalogPath() -> String {
        // Tools/ArmyListStress -> ios/
        let toolDir = URL(fileURLWithPath: #filePath)
            .deletingLastPathComponent() // ArmyListStress
            .deletingLastPathComponent() // Tools
        return toolDir
            .appendingPathComponent("Sources/Experiments/ArmyList/Catalog/Resources/catalog.json")
            .path
    }

    private static func defaultFixturesPath() -> String {
        let iosRoot = URL(fileURLWithPath: #filePath)
            .deletingLastPathComponent()
            .deletingLastPathComponent()
        return iosRoot
            .appendingPathComponent("Tests/PlaygroundTests/Fixtures/ArmyLists")
            .path
    }
}
