import Foundation

/// Prompt plus whether the next call must start a fresh model session.
struct BlatherNarrationRequest: Equatable {
    var prompt: String
    var freshSession: Bool
    var didCompact: Bool
}

/// Decides when Blather's model session should compact.
///
/// The on-device model has a 4096-token window. An open-ended explainer would
/// fill it, so this planner starts a new session with a short carry-over
/// instead of appending forever (TN3193).
struct BlatherPlanner: Equatable {
    private(set) var budget: AgentContextBudget
    private var turns: [OnDeviceContextManager.Turn] = []

    init(windowTokens: Int = AgentContextBudget.defaultWindowTokens) {
        var budget = AgentContextBudget(
            windowTokens: windowTokens,
            toolsReserveTokens: 0,
            usedTokens: 0
        )
        budget.resetBaseline(instructions: BlatherScript.instructions, toolsReserveTokens: 0)
        self.budget = budget
    }

    /// Builds the next prompt. When the estimate is past the compact threshold,
    /// resets the budget and folds older turns into the prompt.
    mutating func makeRequest(topic: String, directions: [String], spoken: [String]) -> BlatherNarrationRequest {
        let tail = spoken.last.map { BlatherScript.tail(of: $0) } ?? ""
        let body = spoken.isEmpty
            ? BlatherScript.opening(topic: topic, directions: directions)
            : BlatherScript.continuation(topic: topic, directions: directions, tail: tail)
        guard budget.needsCompact else {
            return BlatherNarrationRequest(prompt: body, freshSession: false, didCompact: false)
        }
        let summary = OnDeviceContextManager.rollingSummary(turns: turns)
        budget.resetBaseline(instructions: BlatherScript.instructions, toolsReserveTokens: 0)
        turns = []
        let prompt = OnDeviceContextManager.promptWithCarryOver(prompt: body, carryOver: summary)
        return BlatherNarrationRequest(prompt: prompt, freshSession: true, didCompact: true)
    }

    /// Records a prompt that was actually spoken, so the next compact keeps it.
    mutating func commit(prompt: String, speech: String, measuredTotalTokens: Int?) {
        let spoken = speech.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !spoken.isEmpty else { return }
        turns.append(OnDeviceContextManager.Turn(role: .user, content: prompt))
        turns.append(OnDeviceContextManager.Turn(role: .assistant, content: spoken))
        if let measuredTotalTokens {
            budget.reconcileMeasuredUsage(totalTokens: measuredTotalTokens)
        } else {
            budget.addText(prompt)
            budget.addText(spoken)
        }
    }

    /// Forces the next `makeRequest` to compact. Used after a context-window error.
    mutating func forceCompact() {
        budget.usedTokens = budget.windowTokens
    }

    /// Seeds carry-over from audio that was loaded for replay.
    mutating func noteSpoken(_ speech: String) {
        let text = speech.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !text.isEmpty else { return }
        turns.append(OnDeviceContextManager.Turn(role: .assistant, content: text))
        budget.addText(text)
    }
}
