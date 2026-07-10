import Foundation

/// A selectable Mega Man 2–inspired character for the animated widget.
///
/// Sprite frames are original NES-style pixel art (not Capcom rips), stored in
/// `Shared/MegaManWidget/Assets.xcassets` as `{id}_{00…07}`.
struct MegaManCharacter: Identifiable, Hashable, Codable, Sendable {
    let id: String
    let name: String
    /// Number of unique frames in the walk / jump / shoot loop.
    let frameCount: Int

    /// Asset catalog name for frame `index` (wraps).
    func frameAssetName(_ index: Int) -> String {
        let wrapped = ((index % frameCount) + frameCount) % frameCount
        return String(format: "%@_%02d", id, wrapped)
    }

    static let all: [MegaManCharacter] = [
        .init(id: "mega-man", name: "Mega Man", frameCount: 8),
        .init(id: "metal-man", name: "Metal Man", frameCount: 8),
        .init(id: "wood-man", name: "Wood Man", frameCount: 8),
        .init(id: "heat-man", name: "Heat Man", frameCount: 8),
        .init(id: "flash-man", name: "Flash Man", frameCount: 8),
        .init(id: "quick-man", name: "Quick Man", frameCount: 8),
        .init(id: "crash-man", name: "Crash Man", frameCount: 8),
        .init(id: "bubble-man", name: "Bubble Man", frameCount: 8),
        .init(id: "air-man", name: "Air Man", frameCount: 8),
    ]

    static let `default` = all[0]

    static func named(_ id: String) -> MegaManCharacter {
        all.first { $0.id == id } ?? .default
    }
}
