---
name: foundation-models-context
description: >-
  Manage Apple Foundation Models LanguageModelSession context (4096-token
  window). Use when writing or changing on-device FM chat, tools, Generable
  types, compaction, or AgentContextBudget in ios/ (Army List, Device Agent,
  or any new FM experiment).
---

# Foundation Models context window

Apply Apple's guidance from
[TN3193: Managing the on-device foundation model's context window](https://developer.apple.com/documentation/technotes/tn3193-managing-the-on-device-foundation-model-s-context-window)
and
[Managing the context window](https://developer.apple.com/documentation/foundationmodels/managing-the-context-window)
when you add or change on-device Foundation Models code in this repo
(`ios/Sources/Experiments/ArmyList/Chat/`, `ios/Sources/Experiments/DeviceAgent/`,
and any future FM experiment).

The default on-device model has a **4096-token** window per
`LanguageModelSession`. Everything in the session counts toward that budget:
instructions, prompts, tool definitions and their I/O, `@Generable` schemas,
and model replies. When the window is full, the session throws
`LanguageModelSession.GenerationError.exceededContextWindowSize` (also described
as `LanguageModelError.contextSizeExceeded`; often surfaced as a generic
`GenerationError` with code `-1`). The session then cannot take more requests
until you start a new one.

## When to use

Read this skill before you:

- Add or change `LanguageModelSession`, tools, or `@Generable` types
- Tune prompts, session instructions, or chip prompts
- Touch `AgentContextBudget`, `OnDeviceContextManager`, compaction, or context UI meters
- Debug "LLM failed", empty replies after long chats, or tool-loop blowouts

## Hard limits (do not fight these)

| Fact | Implication |
|------|-------------|
| ~4096 tokens per session | Multiturn chat + many tools fills fast |
| Tool schemas are always resident | Every registered `Tool` costs tokens even when unused |
| Tool *results* stay in the transcript | Verbose tool output burns the window for later turns |
| Fresh session = empty memory | Carry over only what the next turn needs |

Prefer Apple's APIs when the deployment target allows them:

- `SystemLanguageModel.default.contextSize` for the real window size
- `SystemLanguageModel.default.tokenCount(for:)` for instructions, prompts, schemas, and transcript entries
- Xcode **Product → Profile → Foundation Models** instrument to see real
  input/output/token growth

This repo's `AgentContextBudget` is a **heuristic** (about 3 characters per
token, reserves for tools and the final reply). Use it for UI meters and
proactive compact. Prefer framework token counts when available; do not treat
the heuristic as exact.

## Stay under budget

### Prompts and instructions

- Keep session instructions short. Imperative verbs. Only what this task needs.
- Cap prompts at about three short paragraphs.
- Chip prompts should send a short `displayText` to the UI transcript and keep
  the long guidance for the model only (Army List already does this).
- Ask for less output when opinion chips are enough ("three bullets", "one
  paragraph"). Prefer that over `GenerationOptions.maximumResponseTokens`, which
  can cut mid-sentence.

### `@Generable` types

- Small types, clear property names.
- Add `@Guide` only when the name is not enough. Guides become schema tokens.
- For arrays, use `@Guide(.maximumCount(_))` so the model cannot emit huge lists.

### Tools

Apple's doc: about **three to five tools** per request when you can. This repo
ships denser tool sets for Army List and Device Agent; if you add more, pay for
them by shrinking descriptions and result payloads.

- Short `name` / `description` / `@Guide` phrases.
- Cap tool result strings before they return to the model
  (`AgentContextBudget.truncateToChars` / `modelFacingSnapshot`).
- Prefer one bulk mutation (`applyRosterPlan`) over loops of tiny tools
  (`addUnit` × N).
- If the model always needs the same facts, put a snapshot in the prompt or
  instructions instead of forcing a tool round-trip every turn.
- Never ask the user for internal IDs. Resolve names in tool code; put
  name→id maps in tool results the model can re-use.

### Split work across sessions

For jobs that cannot fit (long summarize, multi-step plans):

1. New `LanguageModelSession` per chunk.
2. Pass only the previous chunk's summary forward.
3. Combine in a final session.

Do not try to keep one chat session alive through a huge pipeline.

## Recover from overflow (TN3193)

Catch `LanguageModelSession.GenerationError.exceededContextWindowSize` when the
SDK exposes it. Also treat generic generation failures that mention context, or
Army List / Device Agent's known `GenerationError` code `-1`, as overflow (see
`OnDeviceContextManager.isExceededContextWindow`).

Then:

1. Tell the user the context was compacted (Army List / Device Agent already
   append a system line).
2. Start a **new** `LanguageModelSession` with the same tools.
3. Carry only what the next turn needs.

### Apple's preferred seed: first + last transcript entries

```swift
func newContextualSession(
    with originalSession: LanguageModelSession,
    tools: [any Tool]
) -> LanguageModelSession {
    let allEntries = originalSession.transcript
    let condensedEntries = [allEntries.first, allEntries.last].compactMap { $0 }
    let condensedTranscript = Transcript(entries: condensedEntries)
    let newSession = LanguageModelSession(tools: tools, transcript: condensedTranscript)
    newSession.prewarm()
    return newSession
}
```

Playground helpers live in `OnDeviceContextManager` (`rehydratedSession`). Army
List and Device Agent call that on compact when a live session exists, then also
inject a short app-state carry-over (list snapshot or page findings + recent
turns) so the next turn keeps domain state Apple's first/last pair does not
encode.

### Sliding-window rolling summary

When you need more middle-turn memory than first+last alone, keep recent
user/assistant turns intact and compress older ones into a short factual
summary (names, ids, decisions). `OnDeviceContextManager.rollingSummary` builds
that extractively for tests and offline CI; on device you may also ask a *fresh*
short `LanguageModelSession` to merge summaries (never call the overflowing
session). Cap the archive (~1–1.4k characters). Do not wait for overflow: compact
proactively when `AgentContextBudget.needsCompact` is true.

Retry the failed user prompt **once** after compact. If it fails again, stop
and ask the user to Clear or shrink the request.

## Playground map

| Piece | Role |
|-------|------|
| `AgentContextBudget` | Shared estimate, reserves, truncate helpers |
| `OnDeviceContextManager` | Overflow detect, transcript rehydrate, rolling summary |
| `AgentRuntime` | Device Agent session, compact, tool result caps |
| `ArmyListChatRuntime` | List chat session, overflow detect, chip display text |
| Context ring in chat UI | Shows remaining fraction; yellow near compact threshold |

When you change one experiment's FM path, check whether the shared budget
helpers still match Apple's numbers (`defaultWindowTokens = 4096`).

## Checklist before you ship an FM change

- [ ] Instructions and tool descriptions are short enough to skim
- [ ] Tool results returned to the model are capped
- [ ] Bulk edits use one tool call where possible
- [ ] Overflow is detected, compacted (prefer transcript first+last), and
      retried once with a clear user message
- [ ] Carry-over after compact includes the latest user ask (so the model does
      not answer a prior chip)
- [ ] Profiled or at least smoke-tested a long multiturn + tool path

## Official docs

- [TN3193: Managing the on-device foundation model's context window](https://developer.apple.com/documentation/technotes/tn3193-managing-the-on-device-foundation-model-s-context-window)
- [Managing the context window](https://developer.apple.com/documentation/foundationmodels/managing-the-context-window)
- [Prompting an on-device foundation model](https://developer.apple.com/documentation/foundationmodels/prompting-an-on-device-foundation-model)
- [Expanding generation with tool calling](https://developer.apple.com/documentation/foundationmodels/expanding-generation-with-tool-calling)
- [Analyzing the runtime performance of your Foundation Models app](https://developer.apple.com/documentation/foundationmodels/analyzing-the-runtime-performance-of-your-foundation-models-app)
