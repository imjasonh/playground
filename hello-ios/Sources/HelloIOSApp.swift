import SwiftUI

/// App entry point. Kept intentionally tiny — all the interesting, testable
/// logic lives in `TemperatureConverter` and `ConverterViewModel`.
@main
struct HelloIOSApp: App {
    var body: some Scene {
        WindowGroup {
            ContentView()
        }
    }
}
