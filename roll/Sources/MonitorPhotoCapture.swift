import AppKit
import ImageIO
import ScreenCaptureKit
import UniformTypeIdentifiers

enum MonitorPhotoError: LocalizedError {
    case noDisplay
    case unreadableCapture
    case writeFailed(URL)

    var errorDescription: String? {
        switch self {
        case .noDisplay:
            return "No display to capture."
        case .unreadableCapture:
            return "The screenshot couldn't be read."
        case .writeFailed(let url):
            return "Couldn't save \(url.lastPathComponent)."
        }
    }
}

/// Takes a screenshot of the display under the pointer and saves it, run
/// through `MonitorPhotoFilter`, as a JPEG on the Desktop.
enum MonitorPhotoCapture {
    /// Requests Screen Recording access if Roll doesn't have it yet.
    ///
    /// The first request shows the system prompt and returns `false`; macOS
    /// only applies the grant after Roll relaunches.
    static func ensureAccess() -> Bool {
        CGPreflightScreenCaptureAccess() || CGRequestScreenCaptureAccess()
    }

    @MainActor
    static func take(now: Date = Date()) async throws -> URL {
        let screenshot = try await captureDisplayUnderPointer()
        let destination = try desktopURL(for: now)
        let seed = UInt64.random(in: .min ... .max)
        try await Task.detached(priority: .userInitiated) {
            let photo = MonitorPhotoFilter.apply(screenshot, style: .random(seed: seed))
            try writeJPEG(photo, to: destination)
        }.value
        return destination
    }

    @MainActor
    private static func captureDisplayUnderPointer() async throws -> RGBAImage {
        let content = try await SCShareableContent.excludingDesktopWindows(false, onScreenWindowsOnly: true)
        let pointer = NSEvent.mouseLocation
        let screen = NSScreen.screens.first { NSMouseInRect(pointer, $0.frame, false) } ?? NSScreen.main
        let key = NSDeviceDescriptionKey("NSScreenNumber")
        let displayID = (screen?.deviceDescription[key] as? NSNumber)?.uint32Value
        guard let display = content.displays.first(where: { $0.displayID == displayID }) ?? content.displays.first
        else {
            throw MonitorPhotoError.noDisplay
        }

        // Capture in points, not Retina pixels. A phone photo doesn't resolve
        // the extra pixels, and the moiré is tuned to one sample per pixel.
        let configuration = SCStreamConfiguration()
        configuration.width = display.width
        configuration.height = display.height
        configuration.showsCursor = true
        let filter = SCContentFilter(display: display, excludingWindows: [])
        let image = try await SCScreenshotManager.captureImage(contentFilter: filter, configuration: configuration)
        guard let bitmap = RGBAImage(cgImage: image) else {
            throw MonitorPhotoError.unreadableCapture
        }
        return bitmap
    }

    private static func desktopURL(for date: Date) throws -> URL {
        let desktop = try FileManager.default.url(
            for: .desktopDirectory,
            in: .userDomainMask,
            appropriateFor: nil,
            create: false
        )
        let formatter = DateFormatter()
        formatter.locale = Locale(identifier: "en_US_POSIX")
        formatter.dateFormat = "yyyy-MM-dd 'at' HH.mm.ss"
        return desktop.appendingPathComponent("Monitor Photo \(formatter.string(from: date)).jpg")
    }

    private static func writeJPEG(_ image: RGBAImage, to url: URL) throws {
        guard
            let cgImage = image.cgImage(),
            let destination = CGImageDestinationCreateWithURL(url as CFURL, UTType.jpeg.identifier as CFString, 1, nil)
        else {
            throw MonitorPhotoError.writeFailed(url)
        }
        let options = [kCGImageDestinationLossyCompressionQuality: 0.82] as CFDictionary
        CGImageDestinationAddImage(destination, cgImage, options)
        guard CGImageDestinationFinalize(destination) else {
            throw MonitorPhotoError.writeFailed(url)
        }
    }
}

extension RGBAImage {
    init?(cgImage: CGImage) {
        let width = cgImage.width
        let height = cgImage.height
        guard width > 0, height > 0, let space = CGColorSpace(name: CGColorSpace.sRGB) else {
            return nil
        }
        var pixels = [UInt8](repeating: 0, count: width * height * 4)
        let drawn = pixels.withUnsafeMutableBytes { buffer -> Bool in
            guard let context = CGContext(
                data: buffer.baseAddress,
                width: width,
                height: height,
                bitsPerComponent: 8,
                bytesPerRow: width * 4,
                space: space,
                bitmapInfo: CGImageAlphaInfo.noneSkipLast.rawValue
            ) else {
                return false
            }
            context.draw(cgImage, in: CGRect(x: 0, y: 0, width: width, height: height))
            return true
        }
        guard drawn else {
            return nil
        }
        self.init(width: width, height: height, pixels: pixels)
    }

    func cgImage() -> CGImage? {
        guard
            let space = CGColorSpace(name: CGColorSpace.sRGB),
            let provider = CGDataProvider(data: Data(pixels) as CFData)
        else {
            return nil
        }
        return CGImage(
            width: width,
            height: height,
            bitsPerComponent: 8,
            bitsPerPixel: 32,
            bytesPerRow: width * 4,
            space: space,
            bitmapInfo: CGBitmapInfo(rawValue: CGImageAlphaInfo.noneSkipLast.rawValue),
            provider: provider,
            decode: nil,
            shouldInterpolate: false,
            intent: .defaultIntent
        )
    }
}
