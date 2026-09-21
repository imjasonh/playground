import SwiftUI

/// Download / load / phase line for the shared Laya graph. Army List and any
/// other host can show this; the Laya experiment keeps its own richer Model
/// section.
struct LayaModelStatusRow: View {
    @ObservedObject var store: LayaModelStore
    var showsDownloadButton: Bool = true
    var statusIdentifier: String = "layaModelStatus"
    var downloadIdentifier: String = "layaModelDownload"

    var body: some View {
        VStack(alignment: .leading, spacing: 8) {
            HStack(spacing: 8) {
                Image(systemName: symbol)
                    .foregroundStyle(color)
                    .accessibilityHidden(true)
                Text(title)
                    .font(.subheadline)
            }
            .accessibilityElement(children: .combine)
            .accessibilityIdentifier(statusIdentifier)

            if case .downloading(let fraction) = store.phase {
                ProgressView(value: fraction)
                    .accessibilityIdentifier("layaModelDownloadProgress")
            } else if store.phase.isBusy {
                ProgressView()
            } else if showsDownloadButton, !store.isReady {
                Button {
                    Task { await store.prepare() }
                } label: {
                    Text(store.isDownloaded ? "Load Laya" : "Download Laya (\(LayaModelSource.sizeText))")
                }
                .accessibilityIdentifier(downloadIdentifier)
            }
        }
    }

    private var title: String {
        switch store.phase {
        case .notDownloaded:
            return store.isDownloaded ? "Laya downloaded, not loaded" : "Laya not downloaded"
        case .downloading(let fraction):
            return "Downloading Laya \(Int(fraction * 100))%"
        case .verifying:
            return "Verifying Laya"
        case .compiling:
            return "Compiling Laya"
        case .loading:
            return "Loading Laya"
        case .ready:
            return LayaModelStore.isSimulator ? "Laya ready (Simulator: CPU only)" : "Laya ready"
        case .failed(let failure):
            return "Laya failed during \(failure.stage)"
        }
    }

    private var symbol: String {
        switch store.phase {
        case .ready: return "checkmark.circle.fill"
        case .failed: return "exclamationmark.triangle.fill"
        case .notDownloaded: return "circle.dashed"
        default: return "hourglass"
        }
    }

    private var color: Color {
        switch store.phase {
        case .ready: return .green
        case .failed: return .orange
        default: return .secondary
        }
    }
}
