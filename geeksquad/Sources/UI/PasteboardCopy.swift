import AppKit
import Foundation

enum PasteboardCopy {
    static func string(_ text: String) {
        let pb = NSPasteboard.general
        pb.clearContents()
        pb.setString(text, forType: .string)
    }
}
