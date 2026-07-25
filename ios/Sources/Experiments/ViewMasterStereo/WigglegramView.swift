import SwiftUI

/// Alternates left/right images to simulate stereo depth (a wigglegram).
struct WigglegramView: View {
    let left: UIImage
    let right: UIImage
    /// Full left→right→left cycle uses `2 * halfPeriod`.
    var halfPeriod: TimeInterval = 0.22

    @State private var showLeft = true

    var body: some View {
        Image(uiImage: showLeft ? left : right)
            .resizable()
            .scaledToFit()
            .accessibilityIdentifier("viewMasterWigglegram")
            .accessibilityLabel(showLeft ? "Wigglegram left eye" : "Wigglegram right eye")
            .task(id: halfPeriod) {
                showLeft = true
                while !Task.isCancelled {
                    let nanos = UInt64(max(halfPeriod, 0.05) * 1_000_000_000)
                    try? await Task.sleep(nanoseconds: nanos)
                    if Task.isCancelled { break }
                    showLeft.toggle()
                }
            }
    }
}
