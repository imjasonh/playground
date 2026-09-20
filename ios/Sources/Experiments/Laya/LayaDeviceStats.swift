import Foundation

/// Hardware and process facts that explain a timing or a failure.
struct LayaDeviceReport: Equatable {
    let machine: String
    let systemVersion: String
    let physicalMemory: Int64
    let residentMemory: Int64?
    let thermalState: String
    let lowPowerMode: Bool
    let isSimulator: Bool

    var rows: [(String, String)] {
        var rows = [
            ("Device", machine + (isSimulator ? " (Simulator)" : "")),
            ("OS", systemVersion),
            ("Memory", LayaFormat.bytes(physicalMemory)),
            ("Thermal", thermalState),
            ("Low power", lowPowerMode ? "on" : "off"),
        ]
        if let residentMemory {
            rows.append(("Process resident", LayaFormat.bytes(residentMemory)))
        }
        return rows
    }

    var text: String {
        rows.map { "\($0.0): \($0.1)" }.joined(separator: "\n")
    }
}

enum LayaDeviceStats {
    static func report() -> LayaDeviceReport {
        LayaDeviceReport(
            machine: machineIdentifier(),
            systemVersion: ProcessInfo.processInfo.operatingSystemVersionString,
            physicalMemory: Int64(ProcessInfo.processInfo.physicalMemory),
            residentMemory: residentMemoryBytes(),
            thermalState: label(for: ProcessInfo.processInfo.thermalState),
            lowPowerMode: ProcessInfo.processInfo.isLowPowerModeEnabled,
            isSimulator: isSimulator
        )
    }

    static var isSimulator: Bool {
        #if targetEnvironment(simulator)
        return true
        #else
        return false
        #endif
    }

    /// `uname` machine string, for example `iPhone17,1`.
    static func machineIdentifier() -> String {
        var system = utsname()
        uname(&system)
        return withUnsafeBytes(of: &system.machine) { raw in
            String(decoding: raw.prefix { $0 != 0 }, as: UTF8.self)
        }
    }

    /// Resident set size of this process, or nil if the kernel refuses.
    static func residentMemoryBytes() -> Int64? {
        var info = mach_task_basic_info()
        var count = mach_msg_type_number_t(MemoryLayout<mach_task_basic_info>.size / MemoryLayout<natural_t>.size)
        let result = withUnsafeMutablePointer(to: &info) { pointer in
            pointer.withMemoryRebound(to: integer_t.self, capacity: Int(count)) { rebound in
                task_info(mach_task_self_, task_flavor_t(MACH_TASK_BASIC_INFO), rebound, &count)
            }
        }
        guard result == KERN_SUCCESS else { return nil }
        return Int64(info.resident_size)
    }

    static func label(for state: ProcessInfo.ThermalState) -> String {
        switch state {
        case .nominal: return "nominal"
        case .fair: return "fair"
        case .serious: return "serious"
        case .critical: return "critical"
        @unknown default: return "unknown"
        }
    }
}
