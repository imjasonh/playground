import Foundation

/// The four moves, in the order the prompt lists them.
enum LayaSnakeDirection: String, CaseIterable, Equatable {
    case up = "UP"
    case down = "DOWN"
    case left = "LEFT"
    case right = "RIGHT"

    var vector: (dx: Int, dy: Int) {
        switch self {
        case .up: return (0, -1)
        case .down: return (0, 1)
        case .left: return (-1, 0)
        case .right: return (1, 0)
        }
    }
}

struct LayaSnakeCell: Hashable {
    let x: Int
    let y: Int

    init(_ x: Int, _ y: Int) {
        self.x = x
        self.y = y
    }

    func moved(_ direction: LayaSnakeDirection) -> LayaSnakeCell {
        LayaSnakeCell(x + direction.vector.dx, y + direction.vector.dy)
    }
}

struct LayaSnakeMove: Equatable {
    let direction: LayaSnakeDirection
    let legal: Bool
    /// Legal, keeps the tail ahead on the cycle, and does not pass the food.
    let safe: Bool
    /// Cycle positions gained by this move.
    let advance: Int
    let reason: LayaSnakeVerdict
    let eats: Bool
}

/// Why a move is legal or not, in the words the game-over line shows.
enum LayaSnakeVerdict: String, Equatable {
    case legal
    case wall
    case reverse
    case body
    case crossesTail = "would cross the tail"
    case skipsFood = "would skip the food on the safe route"
}

/// SplitMix64. Seeded food placement so a round replays exactly on any device.
struct LayaSnakeRandom: Equatable {
    private var state: UInt64

    init(seed: Int) {
        state = UInt64(bitPattern: Int64(seed))
    }

    mutating func next() -> UInt64 {
        state &+= 0x9E37_79B9_7F4A_7C15
        var z = state
        z = (z ^ (z >> 30)) &* 0xBF58_476D_1CE4_E5B9
        z = (z ^ (z >> 27)) &* 0x94D0_49BB_1331_11EB
        return z ^ (z >> 31)
    }

    mutating func index(below count: Int) -> Int {
        Int(next() % UInt64(count))
    }
}

struct LayaSnakeGame: Equatable {
    let width: Int
    let height: Int
    let seed: Int
    let initialLength: Int
    let cycle: [LayaSnakeCell]
    private let indices: [LayaSnakeCell: Int]
    private var rng: LayaSnakeRandom

    /// Head first.
    private(set) var body: [LayaSnakeCell]
    private(set) var food: LayaSnakeCell?
    private(set) var score = 0
    private(set) var ticks = 0
    private(set) var alive = true
    private(set) var won = false
    private(set) var deathReason: LayaSnakeVerdict?

    var capacity: Int { width * height }
    var head: LayaSnakeCell { body[0] }
    var finished: Bool { !alive || won }

    static let standardWidth = 24
    static let standardHeight = 16
    static let standardInitialLength = 6

    init(width: Int = standardWidth, height: Int = standardHeight, seed: Int = 7, initialLength: Int = standardInitialLength) throws {
        let cycle = try Self.hamiltonianCycle(width: width, height: height)
        guard initialLength >= 2, initialLength < width * height else {
            throw LayaError.invalidQuestion("Initial length must be >= 2 and smaller than the board")
        }
        self.init(width: width, height: height, seed: seed, initialLength: initialLength, cycle: cycle)
    }

    static func standard(seed: Int) -> LayaSnakeGame {
        LayaSnakeGame(
            width: standardWidth, height: standardHeight, seed: seed, initialLength: standardInitialLength,
            cycle: serpentineCycle(width: standardWidth, height: standardHeight)
        )
    }

    private init(width: Int, height: Int, seed: Int, initialLength: Int, cycle: [LayaSnakeCell]) {
        self.width = width
        self.height = height
        self.seed = seed
        self.cycle = cycle
        var indices: [LayaSnakeCell: Int] = [:]
        for (index, cell) in cycle.enumerated() {
            indices[cell] = index
        }
        self.indices = indices
        let capacity = width * height
        self.initialLength = initialLength
        rng = LayaSnakeRandom(seed: seed)
        let start = indices[LayaSnakeCell(width / 2, height / 2)] ?? 0
        body = (0..<initialLength).map { cycle[((start - $0) % capacity + capacity) % capacity] }
        food = nil
        food = spawnFood()
    }

    static func hamiltonianCycle(width: Int, height: Int) throws -> [LayaSnakeCell] {
        guard min(width, height) >= 4, width % 2 == 0 || height % 2 == 0 else {
            throw LayaError.invalidQuestion("Board dimensions must be >= 4, with at least one even dimension")
        }
        if height % 2 == 1 {
            return serpentineCycle(width: height, height: width).map { LayaSnakeCell($0.y, $0.x) }
        }
        return serpentineCycle(width: width, height: height)
    }

    private static func serpentineCycle(width: Int, height: Int) -> [LayaSnakeCell] {
        precondition(height.isMultiple(of: 2), "serpentine cycle needs an even height")
        var path = [LayaSnakeCell(0, 0)]
        for y in 0..<height {
            let xs: [Int] = y % 2 == 0 ? Array(1..<width) : Array(stride(from: width - 1, through: 1, by: -1))
            path.append(contentsOf: xs.map { LayaSnakeCell($0, y) })
        }
        path.append(contentsOf: stride(from: height - 1, through: 1, by: -1).map { LayaSnakeCell(0, $0) })
        return path
    }

    mutating func place(body: [LayaSnakeCell], food: LayaSnakeCell?) throws {
        guard body.count >= 2, body.allSatisfy(contains), Set(body).count == body.count else {
            throw LayaError.invalidQuestion("A placed body needs at least two distinct on-board cells.")
        }
        self.body = body
        self.food = food
    }

    private mutating func spawnFood() -> LayaSnakeCell? {
        let occupied = Set(body)
        let empty = cycle.filter { !occupied.contains($0) }
        guard !empty.isEmpty else { return nil }
        return empty[rng.index(below: empty.count)]
    }

    func target(_ direction: LayaSnakeDirection) -> LayaSnakeCell {
        head.moved(direction)
    }

    func contains(_ cell: LayaSnakeCell) -> Bool {
        (0..<width).contains(cell.x) && (0..<height).contains(cell.y)
    }

    func legalReason(_ direction: LayaSnakeDirection) -> LayaSnakeVerdict {
        let cell = target(direction)
        guard contains(cell) else { return .wall }
        if cell == body[1] { return .reverse }
        var occupied = Set(body)
        if cell != food, let tail = body.last {
            occupied.remove(tail)
        }
        return occupied.contains(cell) ? .body : .legal
    }

    /// Every direction with the planner's verdict. Empty once the game is over.
    func moves() -> [LayaSnakeMove] {
        guard !finished, let tail = body.last else { return [] }
        let headIndex = indices[head] ?? 0
        let tailDistance = ((indices[tail] ?? 0) - headIndex + capacity) % capacity
        let foodDistance = food.flatMap { indices[$0] }.map { ($0 - headIndex + capacity) % capacity } ?? 0
        return LayaSnakeDirection.allCases.map { direction in
            var reason = legalReason(direction)
            let legal = reason == .legal
            let cell = target(direction)
            let advance = ((indices[cell] ?? headIndex) - headIndex + capacity) % capacity
            let eats = cell == food
            var safe = legal
            if safe, advance > tailDistance || (advance == tailDistance && eats) {
                safe = false
                reason = .crossesTail
            }
            if safe, advance == 0 || advance > foodDistance {
                safe = false
                reason = .skipsFood
            }
            return LayaSnakeMove(direction: direction, legal: legal, safe: safe, advance: advance, reason: reason, eats: eats)
        }
    }

    /// Whether the food shares the head's empty region, and that region's size (head included).
    func foodReachability() -> (reachable: Bool, space: Int) {
        var blocked = Set(body)
        blocked.remove(head)
        var visited: Set<LayaSnakeCell> = [head]
        var queue = [head]
        var cursor = 0
        while cursor < queue.count {
            let cell = queue[cursor]
            cursor += 1
            for direction in LayaSnakeDirection.allCases {
                let next = cell.moved(direction)
                if contains(next), !blocked.contains(next), visited.insert(next).inserted {
                    queue.append(next)
                }
            }
        }
        let reachable = food.map { visited.contains($0) } ?? false
        return (reachable, visited.count)
    }

    /// Advances one tick. Returns whether the snake ate.
    @discardableResult
    mutating func step(_ direction: LayaSnakeDirection) throws -> Bool {
        guard !finished else {
            throw LayaError.model("Cannot step a finished game")
        }
        ticks += 1
        let reason = legalReason(direction)
        guard reason == .legal else {
            alive = false
            deathReason = reason
            return false
        }
        let cell = target(direction)
        body.insert(cell, at: 0)
        if cell == food {
            score += 1
            if body.count == capacity {
                won = true
                food = nil
            } else {
                food = spawnFood()
            }
            return true
        }
        body.removeLast()
        return false
    }

    func cycleOrderValid() -> Bool {
        let order = body.reversed().map { indices[$0] ?? 0 }
        let distances = zip(order, order.dropFirst()).map { ($1 - $0 + capacity) % capacity }
        return distances.allSatisfy { $0 > 0 } && distances.reduce(0, +) < capacity
    }
}

struct LayaSnakeTurn: Equatable {
    let state: String
    let moveQuestion: LayaQuestion
    let riskQuestion: LayaQuestion
    let foodQuestion: LayaQuestion
    let safeDirections: [LayaSnakeDirection]
    /// The safe move with the most cycle progress, or nil when trapped.
    let plannerBest: LayaSnakeDirection?
    let foodReachable: Bool
    let openCells: Int
}

struct LayaSnakeDecision: Equatable {
    let probabilities: [LayaSnakeDirection: Double]
    let proposed: LayaSnakeDirection
    let executed: LayaSnakeDirection
    let safeDirections: [LayaSnakeDirection]
    let plannerBest: LayaSnakeDirection?
    var intervened: Bool { proposed != executed }
    /// `1 - P(safe route)`; a model estimate, not a calibrated death probability.
    let deadEndRisk: Double
    let foodReachable: Double
    /// Sum of the three `predict` calls.
    var inferenceSeconds: TimeInterval = 0
    /// Sum of the three `MLModel.prediction` calls.
    var graphSeconds: TimeInterval = 0
    /// Planner plus inference plus bookkeeping.
    var decisionSeconds: TimeInterval = 0
    var inputTokens = 0
}

enum LayaSnakePolicy {
    static let moveInstructions = "Choose the best safe move toward food."
    static let riskInstructions = "Is a safe route available?"
    static let foodInstructions = "Is food reachable through empty cells?"

    /// With the shield on, a board with no safe move throws.
    static func turn(for game: LayaSnakeGame, guarded: Bool) throws -> LayaSnakeTurn {
        let moves = game.moves()
        let safe = moves.filter(\.safe)
        if safe.isEmpty, guarded {
            throw LayaError.model("Cycle safety invariant violated: no safe action")
        }
        let preferred = safe.max { $0.advance < $1.advance }
        let (reachable, space) = game.foodReachability()
        let options = moves.map { move -> LayaChoiceOption in
            let text: String
            if !move.legal {
                text = "Blocked. Collision."
            } else if !move.safe {
                text = "Unsafe. Traps the snake."
            } else if move.eats {
                text = "Safe. Eat food now. Best."
            } else if move.direction == preferred?.direction {
                text = "Safe. Best route to food."
            } else {
                text = "Safe. Slower route."
            }
            return LayaChoiceOption(move.direction.rawValue, text)
        }
        let state = "Safe route: \(safe.isEmpty ? "no" : "yes"). Food reachable through empty cells: \(reachable ? "yes" : "no")."
        return LayaSnakeTurn(
            state: state,
            moveQuestion: .choice(instructions: moveInstructions, options: options),
            riskQuestion: .noul(instructions: riskInstructions),
            foodQuestion: .noul(instructions: foodInstructions),
            safeDirections: safe.map(\.direction),
            plannerBest: preferred?.direction,
            foodReachable: reachable,
            openCells: space
        )
    }

    /// Combines the three answers. The shield swaps an unsafe top-1 for the
    /// most probable safe move and leaves the raw probabilities untouched.
    static func decision(
        turn: LayaSnakeTurn,
        move: LayaDecision,
        risk: LayaDecision,
        food: LayaDecision,
        guarded: Bool
    ) throws -> LayaSnakeDecision {
        guard case .choice(_, let labeled) = move.answer else {
            throw LayaError.model("The move answer is not a choice.")
        }
        guard case .noul(let safeRoute) = risk.answer, case .noul(let reachable) = food.answer else {
            throw LayaError.model("The risk and food answers must be yes/no.")
        }
        var probabilities: [LayaSnakeDirection: Double] = [:]
        for item in labeled {
            guard let direction = LayaSnakeDirection(rawValue: item.label) else {
                throw LayaError.model("Unexpected move label \(item.label).")
            }
            probabilities[direction] = item.probability
        }
        guard probabilities.count == LayaSnakeDirection.allCases.count else {
            throw LayaError.model("Expected a probability for every direction, got \(probabilities.keys.map(\.rawValue).sorted()).")
        }
        let scores = Array(probabilities.values) + [safeRoute, reachable]
        guard scores.allSatisfy({ $0.isFinite && (0...1).contains($0) }) else {
            throw LayaError.model("Model returned an invalid probability; no move executed")
        }
        let proposed = argmax(LayaSnakeDirection.allCases, probabilities)
        let allowed = turn.safeDirections
        let executed = guarded && !allowed.contains(proposed) ? argmax(allowed, probabilities) : proposed
        return LayaSnakeDecision(
            probabilities: probabilities,
            proposed: proposed,
            executed: executed,
            safeDirections: allowed,
            plannerBest: turn.plannerBest,
            deadEndRisk: 1 - safeRoute,
            foodReachable: reachable
        )
    }

    /// First maximum in `candidates` order.
    private static func argmax(_ candidates: [LayaSnakeDirection], _ probabilities: [LayaSnakeDirection: Double]) -> LayaSnakeDirection {
        candidates.max { (probabilities[$0] ?? 0) < (probabilities[$1] ?? 0) } ?? .up
    }
}
