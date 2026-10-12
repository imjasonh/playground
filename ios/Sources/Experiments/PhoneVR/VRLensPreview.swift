import SwiftUI
import simd

/// The panel as the renderer lays it out: each eye's round field, a grid of
/// straight lines pre-warped by the lens model, and the lens axes.
struct VRLensPreview: View {
    let layout: VRStereoLayout

    var body: some View {
        Canvas { context, size in
            let screen = layout.screen
            let scale = min(size.width / CGFloat(screen.widthPixels), size.height / CGFloat(screen.heightPixels))
            let panel = CGSize(width: CGFloat(screen.widthPixels) * scale, height: CGFloat(screen.heightPixels) * scale)
            let origin = CGPoint(x: (size.width - panel.width) / 2, y: (size.height - panel.height) / 2)
            func point(_ p: SIMD2<Float>) -> CGPoint {
                CGPoint(x: origin.x + CGFloat(p.x) * scale, y: origin.y + CGFloat(p.y) * scale)
            }
            let rect = CGRect(origin: origin, size: panel)
            context.fill(Path(roundedRect: rect, cornerRadius: panel.height * 0.12), with: .color(.black))
            var midline = Path()
            midline.move(to: CGPoint(x: rect.midX, y: rect.minY))
            midline.addLine(to: CGPoint(x: rect.midX, y: rect.maxY))
            context.stroke(midline, with: .color(.white.opacity(0.25)), style: StrokeStyle(lineWidth: 1, dash: [3, 3]))

            for eye in VREye.allCases {
                let e = layout[eye]
                let radius = e.fieldRadiusTangent
                var grid = Path()
                let steps = 32
                for fixed in stride(from: -radius, through: radius * 1.0001, by: radius / 4) {
                    for vertical in [true, false] {
                        var drawing = false
                        for i in 0...steps {
                            let moving = -radius + 2 * radius * Float(i) / Float(steps)
                            let t = vertical ? SIMD2(fixed, moving) : SIMD2(moving, fixed)
                            guard simd_length(t) <= radius * 1.0001 else {
                                drawing = false
                                continue
                            }
                            let p = point(layout.pixel(forViewingTangent: t, eye: eye))
                            if drawing { grid.addLine(to: p) } else { grid.move(to: p) }
                            drawing = true
                        }
                    }
                }
                context.stroke(grid, with: .color(.teal.opacity(0.85)), lineWidth: 1)
                let c = point(e.lensCenterPixels)
                let r = CGFloat(e.visibleRadiusPixels) * scale
                context.stroke(Path(ellipseIn: CGRect(x: c.x - r, y: c.y - r, width: 2 * r, height: 2 * r)), with: .color(.white.opacity(0.8)), lineWidth: 1.5)
                var cross = Path()
                cross.move(to: CGPoint(x: c.x - 4, y: c.y))
                cross.addLine(to: CGPoint(x: c.x + 4, y: c.y))
                cross.move(to: CGPoint(x: c.x, y: c.y - 4))
                cross.addLine(to: CGPoint(x: c.x, y: c.y + 4))
                context.stroke(cross, with: .color(.orange), lineWidth: 1.5)
            }
        }
        .aspectRatio(CGFloat(layout.screen.widthPixels) / CGFloat(layout.screen.heightPixels), contentMode: .fit)
        // In landscape the full-width preview would push the rows under it off screen.
        .frame(maxWidth: .infinity, maxHeight: 200)
        .accessibilityElement(children: .ignore)
        .accessibilityLabel("Lens layout on the screen")
        .accessibilityValue(accessibilitySummary)
        .accessibilityIdentifier("phoneVRLensPreview")
    }

    private var accessibilitySummary: String {
        let report = VRViewerReport(layout: layout)
        return String(
            format: "Each eye shows a %.0f-pixel circle whose centre sits %.0f pixels inboard of its half of the screen.",
            report.fieldDiameterPixels,
            report.lensInboardPixels
        )
    }
}
