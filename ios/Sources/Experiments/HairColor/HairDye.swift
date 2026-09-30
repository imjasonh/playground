import CoreImage
import SwiftUI

/// A hair dye swatch. Core Image keeps the hair's luminance and takes hue from this color.
struct HairDye: Identifiable, Equatable {
    let id: String
    let name: String
    let red: CGFloat
    let green: CGFloat
    let blue: CGFloat

    var ciColor: CIColor {
        CIColor(red: red, green: green, blue: blue, alpha: 1)
    }

    var color: Color {
        Color(red: red, green: green, blue: blue)
    }

    /// True when a black checkmark stays readable on the swatch.
    var prefersDarkCheckmark: Bool {
        (0.2126 * red) + (0.7152 * green) + (0.0722 * blue) > 0.62
    }

    static let jet = HairDye(id: "jet", name: "Jet", red: 0.08, green: 0.07, blue: 0.09)
    static let brunette = HairDye(id: "brunette", name: "Brunette", red: 0.28, green: 0.13, blue: 0.06)
    static let auburn = HairDye(id: "auburn", name: "Auburn", red: 0.55, green: 0.15, blue: 0.08)
    static let copper = HairDye(id: "copper", name: "Copper", red: 0.80, green: 0.34, blue: 0.10)
    static let blonde = HairDye(id: "blonde", name: "Blonde", red: 0.91, green: 0.76, blue: 0.42)
    static let silver = HairDye(id: "silver", name: "Silver", red: 0.74, green: 0.77, blue: 0.82)
    static let rose = HairDye(id: "rose", name: "Rose", red: 0.86, green: 0.32, blue: 0.52)
    static let violet = HairDye(id: "violet", name: "Violet", red: 0.40, green: 0.16, blue: 0.74)

    static let all: [HairDye] = [
        jet, brunette, auburn, copper, blonde, silver, rose, violet,
    ]

    static let defaultDye = copper
}
