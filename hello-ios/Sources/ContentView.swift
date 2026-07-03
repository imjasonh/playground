import SwiftUI

/// A tiny temperature converter. Accessibility identifiers are set on the
/// interactive elements so the UI test suite can drive them reliably.
struct ContentView: View {
    @StateObject private var viewModel = ConverterViewModel()

    var body: some View {
        NavigationStack {
            Form {
                Section("Input (\(viewModel.inputUnit))") {
                    TextField("Temperature", text: $viewModel.inputText)
                        .keyboardType(.numbersAndPunctuation)
                        .accessibilityIdentifier("temperatureInput")
                }

                Section("Result") {
                    HStack {
                        Text("Converted")
                        Spacer()
                        Text("\(viewModel.convertedText) \(viewModel.resultUnit)")
                            .monospacedDigit()
                            .accessibilityIdentifier("convertedResult")
                    }

                    Button("Swap scale", action: viewModel.toggleScale)
                        .accessibilityIdentifier("swapButton")
                }
            }
            .navigationTitle("Hello iOS")
        }
    }
}

#Preview {
    ContentView()
}
