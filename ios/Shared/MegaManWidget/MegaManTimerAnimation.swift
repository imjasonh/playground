import SwiftUI

/// Continuous sprite animation for WidgetKit using only public timer APIs.
///
/// Widgets cannot run a normal animation loop: the extension process is not
/// long-lived. This view stacks opaque sprite frames and reveals them with
/// `Text(..., style: .timer)` masks driven by a custom blink font — the
/// technique from Bryce Bostwick's "Apple's Widget Backdoor" (MIT example).
///
/// At 8 FPS with 8 unique frames we duplicate the loop across a 2-second
/// blink period (16 slots) so the stack can hide/show cleanly.
struct MegaManTimerAnimationView: View {
    let character: MegaManCharacter
    /// Frames per second. Keep modest — each frame is a timer + mask.
    var framesPerSecond: Double = 8
    /// Drawn size of the sprite (points).
    var spriteSize: CGFloat = 128

    var body: some View {
        let uniqueFrames = max(character.frameCount, 1)
        // Blink masks have a 2-second period (on 1s / off 1s). Cover both halves.
        let slotCount = max(Int((framesPerSecond * 2).rounded()), uniqueFrames)
        let frameDuration = 1.0 / framesPerSecond
        let half = max(slotCount / 2, 1)

        ZStack {
            ZStack {
                frameView(index: 0, size: spriteSize)
                ForEach(1 ..< half, id: \.self) { slot in
                    frameView(index: slot % uniqueFrames, size: spriteSize)
                        .mask(
                            SimpleBlinkingView(blinkOffset: -Double(slot) * frameDuration)
                                .frame(width: spriteSize, height: spriteSize)
                        )
                }
            }

            ZStack {
                ForEach(half ..< slotCount, id: \.self) { slot in
                    frameView(index: slot % uniqueFrames, size: spriteSize)
                        .mask(
                            SimpleBlinkingView(blinkOffset: -Double(slot) * frameDuration)
                                .frame(width: spriteSize, height: spriteSize)
                        )
                }
            }
            .mask(
                SimpleBlinkingView(blinkOffset: 1)
                    .frame(width: spriteSize, height: spriteSize)
            )
        }
        .frame(width: spriteSize, height: spriteSize)
        .accessibilityLabel("\(character.name) animation")
    }

    @ViewBuilder
    private func frameView(index: Int, size: CGFloat) -> some View {
        Image(character.frameAssetName(index))
            .resizable()
            .interpolation(.none)
            .frame(width: size, height: size)
    }
}

/// Blinks opaque for one second, then transparent for one second, forever.
///
/// Uses `Custom-Regular.otf` (from Bryce Bostwick's MIT WidgetAnimation repo):
/// ligatures map timer digit pairs to a filled or empty square.
struct SimpleBlinkingView: View {
    static let referenceDate = Date().addingTimeInterval(-60)

    var blinkOffset: TimeInterval

    var body: some View {
        GeometryReader { geometry in
            let maxSize = max(geometry.size.width, geometry.size.height)
            Text(Self.referenceDate.addingTimeInterval(-blinkOffset), style: .timer)
                .font(.custom("Custom-Regular", size: maxSize))
                .frame(width: maxSize * 9, height: maxSize, alignment: .trailing)
                .multilineTextAlignment(.trailing)
                .offset(x: -maxSize * 8)
        }
        .clipped()
    }
}

#if DEBUG
#Preview("Mega Man loop") {
    MegaManTimerAnimationView(character: .default)
        .padding()
        .background(Color.black)
}
#endif
