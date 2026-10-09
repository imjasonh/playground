import AppKit

// `@main` only calls `NSApplicationMain`. Without a storyboard, that call
// never assigns `AppDelegate`, so `applicationDidFinishLaunching` never runs.
// `NSApplication.delegate` does not retain its value, so this local has to
// stay alive across `app.run()`.
let app = NSApplication.shared
let delegate = AppDelegate()
app.delegate = delegate
app.run()
