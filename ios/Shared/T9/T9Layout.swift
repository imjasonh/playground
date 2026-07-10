import Foundation

/// One physical key on a classic 12-key phone pad.
enum T9PadKey: Hashable, Sendable {
    case digit(Int) // 0...9
    case star
    case hash

    /// ITU E.161 letter layout used by old Nokia-style multi-tap phones.
    var letters: [Character] {
        switch self {
        case .digit(1): return Array(".,?!'\"1-()@/:;")
        case .digit(2): return Array("abc2")
        case .digit(3): return Array("def3")
        case .digit(4): return Array("ghi4")
        case .digit(5): return Array("jkl5")
        case .digit(6): return Array("mno6")
        case .digit(7): return Array("pqrs7")
        case .digit(8): return Array("tuv8")
        case .digit(9): return Array("wxyz9")
        case .digit(0): return Array(" 0")
        case .digit, .star, .hash: return []
        }
    }

    /// Digit / symbol inserted on long-press (bypasses multi-tap cycling).
    var longPressCharacter: Character? {
        switch self {
        case .digit(let n) where (0...9).contains(n):
            return Character(String(n))
        case .star: return "*"
        case .hash: return "#"
        case .digit: return nil
        }
    }

    var digitValue: Int? {
        if case .digit(let n) = self { return n }
        return nil
    }

    /// Secondary label shown under the main key title (e.g. "abc").
    var subtitle: String {
        switch self {
        case .digit(1): return ".,?!"
        case .digit(2): return "ABC"
        case .digit(3): return "DEF"
        case .digit(4): return "GHI"
        case .digit(5): return "JKL"
        case .digit(6): return "MNO"
        case .digit(7): return "PQRS"
        case .digit(8): return "TUV"
        case .digit(9): return "WXYZ"
        case .digit(0): return "_"
        case .star: return "SHIFT"
        case .hash: return "SPACE"
        case .digit: return ""
        }
    }

    var title: String {
        switch self {
        case .digit(let n): return String(n)
        case .star: return "*"
        case .hash: return "#"
        }
    }
}

/// Input casing / digit mode, cycled with `*` like many feature phones.
enum T9ShiftMode: String, CaseIterable, Equatable, Sendable {
    /// Next letters are lowercase (`abc`).
    case lowercase
    /// Next letter only is uppercase, then returns to lowercase (`Abc`).
    case uppercaseOnce
    /// All letters uppercase (`ABC`).
    case capsLock
    /// Digit keys insert their number immediately (`123`).
    case numbers

    var label: String {
        switch self {
        case .lowercase: return "abc"
        case .uppercaseOnce: return "Abc"
        case .capsLock: return "ABC"
        case .numbers: return "123"
        }
    }

    func next() -> T9ShiftMode {
        switch self {
        case .lowercase: return .uppercaseOnce
        case .uppercaseOnce: return .capsLock
        case .capsLock: return .numbers
        case .numbers: return .lowercase
        }
    }
}

/// Standard phone-pad rows: 1–9, then * 0 #.
enum T9PadLayout {
    static let rows: [[T9PadKey]] = [
        [.digit(1), .digit(2), .digit(3)],
        [.digit(4), .digit(5), .digit(6)],
        [.digit(7), .digit(8), .digit(9)],
        [.star, .digit(0), .hash],
    ]
}
