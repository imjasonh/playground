enum DieFace: Int, CaseIterable, Equatable, Sendable {
    case one = 1
    case two
    case three
    case four
    case five
    case six

    var symbolName: String {
        "die.face.\(rawValue)"
    }
}

struct Die: Equatable, Sendable {
    private(set) var face: DieFace?

    var symbolName: String {
        if let face {
            return face.symbolName
        }
        return "dice"
    }

    var statusText: String {
        if let face {
            return "Showing \(face.rawValue)"
        }
        return "Not rolled yet"
    }

    static func fairFace() -> DieFace {
        DieFace.allCases.randomElement() ?? .one
    }

    @discardableResult
    mutating func roll() -> DieFace {
        roll { Die.fairFace() }
    }

    @discardableResult
    mutating func roll(nextFace: () -> DieFace) -> DieFace {
        let rolled = nextFace()
        face = rolled
        return rolled
    }
}
