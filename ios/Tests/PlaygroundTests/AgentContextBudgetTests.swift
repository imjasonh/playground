import XCTest
@testable import Playground

final class AgentContextBudgetTests: XCTestCase {
    func testEstimatesAndTruncates() {
        XCTAssertEqual(AgentContextBudget.estimateTokens(""), 0)
        XCTAssertEqual(AgentContextBudget.estimateTokens("abc"), 1)
        XCTAssertEqual(AgentContextBudget.estimateTokens(String(repeating: "a", count: 12)), 4)

        var budget = AgentContextBudget()
        budget.resetBaseline(instructions: String(repeating: "i", count: 300), toolsReserveTokens: 900)
        XCTAssertGreaterThan(budget.fractionUsed, 0)
        XCTAssertLessThan(budget.fractionUsed, AgentContextBudget.compactThreshold)
        XCTAssertFalse(budget.needsCompact)

        budget.addTokens(2_500)
        XCTAssertTrue(budget.needsCompact)
        XCTAssertGreaterThanOrEqual(budget.percentUsed, 72)

        budget.reconcileMeasuredUsage(totalTokens: 2_000)
        XCTAssertEqual(budget.committedTokens, 2_000)

        let truncated = AgentContextBudget.truncateToChars(String(repeating: "x", count: 100), maxChars: 20)
        XCTAssertEqual(truncated.count, 20)
        XCTAssertTrue(truncated.hasSuffix("…"))
    }
}
