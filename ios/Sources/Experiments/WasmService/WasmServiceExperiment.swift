import SwiftUI

/// Registration entry for the Wasm Service experiment.
enum WasmServiceExperiment {
    static let experiment = Experiment(
        id: "wasm-service",
        title: "Wasm Service",
        summary: "Pull a WebAssembly module from a registry and serve it over HTTP from this phone.",
        icon: "server.rack"
    ) {
        WasmServiceView()
    }
}
