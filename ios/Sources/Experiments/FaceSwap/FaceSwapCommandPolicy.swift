import CoreGraphics
import Foundation

/// Keeps the smallest edit that matches the request.
///
/// The on-device model picks ids. It also calls extra tools. A face swap
/// must not also paste or erase a person rectangle.
enum FaceSwapCommandPolicy {
    static func select(
        _ commands: [FaceSwapCommand],
        request: String,
        regions: [FaceSwapRegion]
    ) -> [FaceSwapCommand] {
        switch intent(of: request) {
        case .replaceFaces:
            return faceEdits(commands, request: request, regions: regions)
        case .remove:
            return Array(commands.filter(isRemove).prefix(1))
        case .copy:
            return Array(commands.filter(isCopy).prefix(1))
        case .unspecified:
            if commands.contains(where: isReplace) {
                return faceEdits(commands, request: request, regions: regions)
            }
            return Array(commands.prefix(1))
        }
    }

    private enum Intent {
        case replaceFaces
        case remove
        case copy
        case unspecified
    }

    private static func intent(of request: String) -> Intent {
        let text = request.lowercased()
        let erase = contains(text, ["remove", "erase", "delete", "get rid"])
        let duplicate = contains(text, ["duplicate", "another of", "copies of", "5 of", "five of"])
        let faceEdit = contains(text, ["face", "swap", "onto"])
        if faceEdit && !erase {
            return .replaceFaces
        }
        if erase && !duplicate {
            return .remove
        }
        if duplicate {
            return .copy
        }
        return .unspecified
    }

    private static func faceEdits(
        _ commands: [FaceSwapCommand],
        request: String,
        regions: [FaceSwapRegion]
    ) -> [FaceSwapCommand] {
        let faces = regions.filter { $0.kind == .face }
        if isMutualSwap(request), faces.count == 2, let first = faces.first, let second = faces.last {
            let plan = FaceSwapEditPlan.identity.clamped()
            return [
                .replaceFaces(sourceID: first.id, destinationIDs: [second.id], plan: plan),
                .replaceFaces(sourceID: second.id, destinationIDs: [first.id], plan: plan),
            ]
        }
        guard let command = commands.first(where: isReplace),
              case .replaceFaces(let sourceID, let destinationIDs, let plan) = command
        else {
            return []
        }
        let destinations = limitedDestinations(destinationIDs, sourceID: sourceID, request: request)
        guard !destinations.isEmpty else { return [] }
        return [.replaceFaces(sourceID: sourceID, destinationIDs: destinations, plan: plan)]
    }

    private static func isMutualSwap(_ request: String) -> Bool {
        let text = request.lowercased()
        if contains(text, ["onto", "every", "all ", "each", "both"]) {
            return false
        }
        return text.contains("swap")
    }

    private static func limitedDestinations(_ ids: [String], sourceID: String, request: String) -> [String] {
        var seen = Set<String>()
        var destinations: [String] = []
        for id in ids where id.lowercased() != sourceID.lowercased() {
            let key = id.lowercased()
            if seen.insert(key).inserted {
                destinations.append(id)
            }
        }
        let text = request.lowercased()
        if contains(text, ["every", "all ", "each", "both"]) {
            return destinations
        }
        return Array(destinations.prefix(1))
    }

    private static func isRemove(_ command: FaceSwapCommand) -> Bool {
        if case .remove = command { return true }
        return false
    }

    private static func isCopy(_ command: FaceSwapCommand) -> Bool {
        if case .copy = command { return true }
        return false
    }

    private static func isReplace(_ command: FaceSwapCommand) -> Bool {
        if case .replaceFaces = command { return true }
        return false
    }

    private static func contains(_ text: String, _ needles: [String]) -> Bool {
        needles.contains { text.contains($0) }
    }
}
