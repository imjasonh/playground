import Foundation

/// Metal Man sprite set for the animated Home Screen widget.
///
/// Frames are sliced from `Shared/MegaManWidget/SourcesSheets/metal-man.gif`
/// into `{id}_{00…07}` images in the asset catalog.
struct MegaManCharacter: Identifiable, Hashable, Codable, Sendable {
    let id: String
    let name: String
    /// Number of unique frames in the walk / throw / jump loop.
    let frameCount: Int

    /// Asset catalog name for frame `index` (wraps).
    func frameAssetName(_ index: Int) -> String {
        let wrapped = ((index % frameCount) + frameCount) % frameCount
        return String(format: "%@_%02d", id, wrapped)
    }

    static let metalMan = MegaManCharacter(id: "metal-man", name: "Metal Man", frameCount: 16)

    static let all: [MegaManCharacter] = [.metalMan]

    static let `default` = metalMan
}
