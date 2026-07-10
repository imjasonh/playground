import Foundation

/// Pure multi-tap (old Nokia-style) input engine.
///
/// Repeated taps on the same key within ``commitDelay`` cycle that key's
/// letters; a different key, timeout, or explicit commit inserts the pending
/// character. `*` cycles shift/number mode; `#` inserts a space.
final class T9MultiTapEngine: @unchecked Sendable {
    /// How long to wait before committing the currently cycling letter.
    var commitDelay: TimeInterval = 1.0

    private(set) var shiftMode: T9ShiftMode = .lowercase
    private(set) var pendingKey: T9PadKey?
    private(set) var pendingIndex: Int = 0

    /// Character currently being cycled (not yet committed), if any.
    var pendingCharacter: Character? {
        guard let key = pendingKey else { return nil }
        return character(for: key, at: pendingIndex)
    }

    /// Preview string for the pending character (empty when none).
    var pendingPreview: String {
        pendingCharacter.map(String.init) ?? ""
    }

    private var commitWorkItem: DispatchWorkItem?
    private let queue: DispatchQueue
    private let onInsert: (String) -> Void
    private let onDeleteBackward: () -> Void
    private let onStateChange: () -> Void

    /// - Parameters:
    ///   - queue: Queue used for the commit timer. Defaults to main (UI).
    ///   - onInsert: Called with text to insert into the document.
    ///   - onDeleteBackward: Called to delete one character before the cursor.
    ///   - onStateChange: Called whenever pending/shift state changes (for UI).
    init(
        queue: DispatchQueue = .main,
        onInsert: @escaping (String) -> Void,
        onDeleteBackward: @escaping () -> Void,
        onStateChange: @escaping () -> Void = {}
    ) {
        self.queue = queue
        self.onInsert = onInsert
        self.onDeleteBackward = onDeleteBackward
        self.onStateChange = onStateChange
    }

    deinit {
        commitWorkItem?.cancel()
    }

    // MARK: - Input

    /// Handle a short tap on a pad key.
    func tap(_ key: T9PadKey) {
        switch key {
        case .star:
            commitPending()
            shiftMode = shiftMode.next()
            notify()
        case .hash:
            commitPending()
            onInsert(" ")
            notify()
        case .digit:
            handleDigitTap(key)
        }
    }

    /// Long-press inserts the key's digit/symbol immediately (no multi-tap).
    func longPress(_ key: T9PadKey) {
        guard let ch = key.longPressCharacter else { return }
        commitPending()
        onInsert(String(ch))
        notify()
    }

    func deleteBackward() {
        if pendingKey != nil {
            cancelPending(commit: false)
            notify()
            return
        }
        onDeleteBackward()
        notify()
    }

    /// Force-commit any pending multi-tap character (e.g. before dismissing).
    func commitPending() {
        guard let key = pendingKey else { return }
        let ch = character(for: key, at: pendingIndex)
        cancelPending(commit: false)
        if let ch {
            onInsert(String(applyShift(ch)))
            advanceShiftAfterLetter()
        }
        notify()
    }

    // MARK: - Internals

    private func handleDigitTap(_ key: T9PadKey) {
        if shiftMode == .numbers {
            commitPending()
            if let ch = key.longPressCharacter {
                onInsert(String(ch))
            }
            notify()
            return
        }

        let letters = key.letters
        guard !letters.isEmpty else { return }

        if pendingKey == key {
            pendingIndex = (pendingIndex + 1) % letters.count
            scheduleCommit()
            notify()
            return
        }

        commitPending()
        pendingKey = key
        pendingIndex = 0
        scheduleCommit()
        notify()
    }

    private func character(for key: T9PadKey, at index: Int) -> Character? {
        let letters = key.letters
        guard !letters.isEmpty else { return nil }
        let i = ((index % letters.count) + letters.count) % letters.count
        return letters[i]
    }

    private func applyShift(_ ch: Character) -> Character {
        guard ch.isLetter else { return ch }
        switch shiftMode {
        case .lowercase, .numbers:
            return Character(ch.lowercased())
        case .uppercaseOnce, .capsLock:
            return Character(ch.uppercased())
        }
    }

    private func advanceShiftAfterLetter() {
        if shiftMode == .uppercaseOnce {
            shiftMode = .lowercase
        }
    }

    private func scheduleCommit() {
        commitWorkItem?.cancel()
        let work = DispatchWorkItem { [weak self] in
            self?.commitPending()
        }
        commitWorkItem = work
        queue.asyncAfter(deadline: .now() + commitDelay, execute: work)
    }

    private func cancelPending(commit: Bool) {
        commitWorkItem?.cancel()
        commitWorkItem = nil
        if commit, let key = pendingKey, let ch = character(for: key, at: pendingIndex) {
            onInsert(String(applyShift(ch)))
            advanceShiftAfterLetter()
        }
        pendingKey = nil
        pendingIndex = 0
    }

    private func notify() {
        onStateChange()
    }
}
