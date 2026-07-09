import SwiftUI

/// First experiment: a tiny temperature converter. Navigation (title/back) is
/// provided by the launcher, so this view is just the content. Accessibility
/// identifiers are set on interactive elements for the UI tests.
struct TemperatureConverterView: View {
    @StateObject private var viewModel = ConverterViewModel()

    var body: some View {
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
    }
}

#Preview {
    NavigationStack {
        TemperatureConverterView()
            .navigationTitle("Temperature Converter")
    }
}
