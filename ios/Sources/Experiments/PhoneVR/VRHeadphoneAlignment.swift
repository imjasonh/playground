import Foundation
import simd

/// One rotation-sensor sample from the phone or from AirPods.
struct VRRotationSample {
    var timestamp: TimeInterval
    /// Body-frame angular velocity, radians per second.
    var rate: SIMD3<Float>
    /// Reference-from-body attitude in that sensor's own reference frame.
    var attitude: simd_quatf
}

/// Signal tools for lining up two rotation sensors on the same rigid head.
enum VRSignalAlignment {
    /// Sample interpolated at `time`, or nil outside the stream. `cursor`
    /// caches the search position for ascending queries.
    static func interpolate(_ samples: [VRRotationSample], at time: Double, cursor: inout Int) -> VRRotationSample? {
        guard let first = samples.first, let last = samples.last,
              time >= first.timestamp, time <= last.timestamp else { return nil }
        if samples.count == 1 { return first }
        cursor = min(max(cursor, 0), samples.count - 2)
        while cursor > 0, samples[cursor].timestamp > time { cursor -= 1 }
        while cursor < samples.count - 2, samples[cursor + 1].timestamp < time { cursor += 1 }
        let a = samples[cursor]
        let b = samples[cursor + 1]
        let span = b.timestamp - a.timestamp
        let f = span > 0 ? Float((time - a.timestamp) / span) : 0
        return VRRotationSample(
            timestamp: time,
            rate: a.rate + (b.rate - a.rate) * f,
            attitude: simd_slerp(a.attitude, b.attitude, f)
        )
    }

    /// Pearson correlation of two equal-length series, or nil when either is flat.
    static func correlation(_ a: [Float], _ b: [Float]) -> Float? {
        guard a.count == b.count, a.count > 2 else { return nil }
        let n = Float(a.count)
        let meanA = a.reduce(0, +) / n
        let meanB = b.reduce(0, +) / n
        var covariance: Float = 0
        var varianceA: Float = 0
        var varianceB: Float = 0
        for i in 0..<a.count {
            let da = a[i] - meanA
            let db = b[i] - meanB
            covariance += da * db
            varianceA += da * da
            varianceB += db * db
        }
        guard varianceA > 1e-9, varianceB > 1e-9 else { return nil }
        return covariance / (varianceA * varianceB).squareRoot()
    }

    /// Delay of `delayed` behind `reference`, found by cross-correlating the
    /// rotation-rate magnitudes. Magnitudes don't depend on either sensor's
    /// axes, so this works before the mounting rotation is known. A positive
    /// lag means `delayed`'s timestamps run late.
    static func estimateLag(
        reference: [VRRotationSample],
        delayed: [VRRotationSample],
        gridStep: Double,
        lags: ClosedRange<Double>,
        lagStep: Double
    ) -> (lag: Double, correlation: Float)? {
        guard let refFirst = reference.first, let refLast = reference.last,
              let delFirst = delayed.first, let delLast = delayed.last else { return nil }
        let start = max(refFirst.timestamp, delFirst.timestamp - lags.lowerBound)
        let end = min(refLast.timestamp, delLast.timestamp - lags.upperBound)
        guard end - start > 1 else { return nil }

        var grid: [Double] = []
        var t = start
        while t <= end {
            grid.append(t)
            t += gridStep
        }
        var cursor = 0
        let rawMagnitudes = grid.compactMap { interpolate(reference, at: $0, cursor: &cursor).map { simd_length($0.rate) } }
        guard rawMagnitudes.count == grid.count else { return nil }
        // Low-pass the faster stream so both have about the same bandwidth.
        let referenceMagnitudes = movingAverage(rawMagnitudes, radius: 2)

        var best: (lag: Double, correlation: Float)?
        var scores: [(lag: Double, correlation: Float)] = []
        var lag = lags.lowerBound
        while lag <= lags.upperBound + 1e-9 {
            var delayedCursor = 0
            let magnitudes = grid.compactMap { interpolate(delayed, at: $0 + lag, cursor: &delayedCursor).map { simd_length($0.rate) } }
            if magnitudes.count == grid.count, let r = correlation(referenceMagnitudes, magnitudes) {
                scores.append((lag, r))
                if best == nil || r > (best?.correlation ?? -1) { best = (lag, r) }
            }
            lag += lagStep
        }
        guard let peak = best, let index = scores.firstIndex(where: { $0.lag == peak.lag }) else { return nil }
        guard index > 0, index < scores.count - 1 else { return peak }
        let c0 = scores[index - 1].correlation
        let c1 = peak.correlation
        let c2 = scores[index + 1].correlation
        let denominator = c0 - 2 * c1 + c2
        guard abs(denominator) > 1e-9 else { return peak }
        let offset = Double(0.5 * (c0 - c2) / denominator)
        return (peak.lag + min(max(offset, -1), 1) * lagStep, peak.correlation)
    }

    static func movingAverage(_ values: [Float], radius: Int) -> [Float] {
        guard radius > 0, values.count > 1 else { return values }
        var out = [Float](repeating: 0, count: values.count)
        for i in 0..<values.count {
            let lo = max(0, i - radius)
            let hi = min(values.count - 1, i + radius)
            var sum: Float = 0
            for j in lo...hi { sum += values[j] }
            out[i] = sum / Float(hi - lo + 1)
        }
        return out
    }

    /// Rotation that best maps `source` vectors onto `target` vectors in the
    /// least-squares sense (Horn's quaternion method). `confidence` is the gap
    /// between the two largest eigenvalues relative to the largest; it falls
    /// toward 0 when the motion only spans one axis.
    static func fitRotation(from source: [SIMD3<Float>], to target: [SIMD3<Float>]) -> (rotation: simd_quatf, confidence: Float)? {
        guard source.count == target.count, source.count >= 3 else { return nil }
        var s = [[Double]](repeating: [0, 0, 0], count: 3)
        for (a, b) in zip(source, target) {
            let av = [Double(a.x), Double(a.y), Double(a.z)]
            let bv = [Double(b.x), Double(b.y), Double(b.z)]
            for i in 0..<3 {
                for j in 0..<3 {
                    s[i][j] += av[i] * bv[j]
                }
            }
        }
        let sxx = s[0][0], sxy = s[0][1], sxz = s[0][2]
        let syx = s[1][0], syy = s[1][1], syz = s[1][2]
        let szx = s[2][0], szy = s[2][1], szz = s[2][2]
        let n: [[Double]] = [
            [sxx + syy + szz, syz - szy, szx - sxz, sxy - syx],
            [syz - szy, sxx - syy - szz, sxy + syx, szx + sxz],
            [szx - sxz, sxy + syx, -sxx + syy - szz, syz + szy],
            [sxy - syx, szx + sxz, syz + szy, -sxx - syy + szz],
        ]
        let (values, vectors) = symmetricEigen(n)
        let order = values.indices.sorted { values[$0] > values[$1] }
        let top = order[0]
        let q = (0..<4).map { vectors[$0][top] }
        let rotation = simd_quatf(ix: Float(q[1]), iy: Float(q[2]), iz: Float(q[3]), r: Float(q[0])).normalized
        let largest = values[top]
        let gap = largest - values[order[1]]
        let confidence = largest > 1e-12 ? Float(gap / largest) : 0
        return (rotation, confidence)
    }

    /// Eigenvalues and eigenvectors (as columns) of a small symmetric matrix,
    /// by cyclic Jacobi rotations.
    static func symmetricEigen(_ matrix: [[Double]]) -> (values: [Double], vectors: [[Double]]) {
        let size = matrix.count
        var a = matrix
        var v = (0..<size).map { i in (0..<size).map { j in i == j ? 1.0 : 0.0 } }
        for _ in 0..<64 {
            var off = 0.0
            for p in 0..<size {
                for q in (p + 1)..<size { off += a[p][q] * a[p][q] }
            }
            if off < 1e-22 { break }
            for p in 0..<(size - 1) {
                for q in (p + 1)..<size where abs(a[p][q]) > 1e-300 {
                    let theta = (a[q][q] - a[p][p]) / (2 * a[p][q])
                    let t = (theta >= 0 ? 1.0 : -1.0) / (abs(theta) + (theta * theta + 1).squareRoot())
                    let c = 1 / (t * t + 1).squareRoot()
                    let s = t * c
                    for k in 0..<size {
                        let akp = a[k][p]
                        let akq = a[k][q]
                        a[k][p] = c * akp - s * akq
                        a[k][q] = s * akp + c * akq
                    }
                    for k in 0..<size {
                        let apk = a[p][k]
                        let aqk = a[q][k]
                        a[p][k] = c * apk - s * aqk
                        a[q][k] = s * apk + c * aqk
                    }
                    for k in 0..<size {
                        let vkp = v[k][p]
                        let vkq = v[k][q]
                        v[k][p] = c * vkp - s * vkq
                        v[k][q] = s * vkp + c * vkq
                    }
                }
            }
        }
        return ((0..<size).map { a[$0][$0] }, v)
    }
}

/// Uses AirPods head tracking as a slow second opinion on the phone's IMU.
///
/// The phone is strapped to the same head and its IMU is faster, so AirPods
/// never drive the image. Each tick (about once a second) this estimates how
/// late the AirPods samples arrive and how the earbuds are turned relative to
/// the phone, then compares the two sensors' rotations since a reference time.
/// For a rigid strap that residual stays near zero: a lasting step while the
/// head is still means the viewer slipped on the face, and a slow yaw creep
/// is gyro drift, which matters only with the camera off.
struct VRHeadphoneCrossCheck {
    struct Configuration {
        var window: TimeInterval = 5
        var gridStep: Double = 0.01
        var lags: ClosedRange<Double> = -0.05...0.30
        var lagStep: Double = 0.005
        var minimumCorrelation: Float = 0.6
        /// Spread of the phone's rotation speed needed before estimating, radians per second.
        var minimumMotion: Float = 0.2
        var minimumFitConfidence: Float = 0.1
        /// Only samples faster than this inform the mounting fit, radians per second.
        var fitSpeed: Float = 0.3
        var estimateSmoothing: Double = 0.3
        var slipThreshold: Float = VRMath.radians(4)
        var slipTicks = 2
        /// Head speed below which a residual step counts as a slip, radians per second.
        var stillHeadSpeed: Float = 0.6
        var baselineTimeConstant: TimeInterval = 20
        /// Time constant for the camera-off yaw bias.
        var yawTimeConstant: TimeInterval = 30
        var stableLocationDuration: TimeInterval = 2
        var staleAfter: TimeInterval = 0.5
    }

    enum Status: Equatable {
        case waitingForAirPods
        case needsMotion
        case aligned
    }

    struct Snapshot: Equatable {
        var status: Status
        /// How late AirPods timestamps run behind the phone's, seconds.
        var latency: Double?
        var correlation: Float?
        /// Earbud-to-phone mounting rotation as a rotation vector, degrees.
        var mountRotationDegrees: SIMD3<Float>?
        var residualDegrees: Float?
        var updateRateHz: Double?
        var slipCount: Int
        var lastSlipTime: TimeInterval?
        /// Yaw bias the head tracker should ease toward with the camera off.
        var yawBiasTarget: Float
    }

    var configuration = Configuration()
    private(set) var latency: Double?
    private(set) var correlation: Float?
    /// Maps earbud body vectors into phone body vectors.
    private(set) var mountRotation: simd_quatf?
    private var reference: (time: Double, phone: simd_quatf, pods: simd_quatf, bias: Float)?
    private var baseline: Float = 0
    private var excessTicks = 0
    private(set) var slipCount = 0
    private(set) var lastSlipTime: TimeInterval?
    private var location: (value: Int, since: Double)?
    private(set) var yawBiasTarget: Float = 0
    private var lastTick: Double?
    private var residualDegrees: Float?

    mutating func resetAlignment() {
        latency = nil
        correlation = nil
        mountRotation = nil
        reference = nil
        baseline = 0
        excessTicks = 0
        residualDegrees = nil
    }

    /// Runs one tick over the newest samples. `podsLocation` identifies which
    /// earbud reports motion; a change restarts the alignment.
    mutating func update(
        phone allPhone: [VRRotationSample],
        pods allPods: [VRRotationSample],
        podsLocation: Int,
        now: Double,
        currentYawBias: Float
    ) -> Snapshot {
        let dt = lastTick.map { now - $0 } ?? 0
        lastTick = now
        let c = configuration
        let phone = allPhone.filter { $0.timestamp >= now - c.window }
        let pods = allPods.filter { $0.timestamp >= now - c.window - (c.lags.upperBound) }
        let rate = Self.rate(of: pods)

        guard let newestPods = pods.last, newestPods.timestamp >= now - c.staleAfter, phone.count > 10 else {
            return snapshot(.waitingForAirPods, rate: rate)
        }
        if location?.value != podsLocation {
            location = (podsLocation, now)
            resetAlignment()
        }
        guard let since = location?.since, now - since >= c.stableLocationDuration else {
            return snapshot(.waitingForAirPods, rate: rate)
        }

        let speeds = phone.map { simd_length($0.rate) }
        if Self.standardDeviation(speeds) >= c.minimumMotion {
            estimateLatencyAndMount(phone: phone, pods: pods)
        }
        guard let latency, let mount = mountRotation else {
            return snapshot(.needsMotion, rate: rate)
        }

        let commonTime = min(phone.last?.timestamp ?? now, newestPods.timestamp - latency)
        var phoneCursor = 0
        var podsCursor = 0
        guard let phoneNow = VRSignalAlignment.interpolate(phone, at: commonTime, cursor: &phoneCursor),
              let podsNow = VRSignalAlignment.interpolate(pods, at: commonTime + latency, cursor: &podsCursor) else {
            return snapshot(.aligned, rate: rate)
        }
        guard let ref = reference else {
            reference = (commonTime, phoneNow.attitude, podsNow.attitude, currentYawBias)
            baseline = 0
            residualDegrees = 0
            return snapshot(.aligned, rate: rate)
        }

        let phoneDelta = ref.phone.inverse * phoneNow.attitude
        let podsDelta = mount * (ref.pods.inverse * podsNow.attitude) * mount.inverse
        let residual = (phoneDelta * podsDelta.inverse).normalized
        let angle = VRMath.angleBetween(residual, VRMath.identityRotation)
        residualDegrees = VRMath.degrees(angle)

        let recent = phone.filter { $0.timestamp >= commonTime - 0.5 }.map { simd_length($0.rate) }
        let headSpeed = recent.isEmpty ? 0 : recent.reduce(0, +) / Float(recent.count)
        if headSpeed < c.stillHeadSpeed {
            if abs(angle - baseline) > c.slipThreshold {
                excessTicks += 1
                if excessTicks >= c.slipTicks {
                    slipCount += 1
                    lastSlipTime = now
                    reference = nil
                    baseline = 0
                    excessTicks = 0
                    // The phone now sits differently on the head, so refit the mounting.
                    mountRotation = nil
                    return snapshot(.aligned, rate: rate)
                }
            } else {
                excessTicks = 0
                baseline += (angle - baseline) * VRMath.blendFactor(dt: dt, tau: c.baselineTimeConstant)
            }
        }

        // Yaw creep in Core Motion's reference frame, which has z up. Splitting
        // the difference between two independent gyros halves the drift variance.
        let worldResidual = (ref.phone * residual * ref.phone.inverse).normalized
        let twist = VRMath.twist(of: worldResidual, about: SIMD3(0, 0, 1))
        let residualYaw = VRMath.wrapAngle(2 * atan2(twist.imag.z, twist.real))
        let target = ref.bias - 0.5 * residualYaw
        yawBiasTarget += (target - yawBiasTarget) * VRMath.blendFactor(dt: dt, tau: c.yawTimeConstant)
        return snapshot(.aligned, rate: rate)
    }

    // MARK: - Private

    private mutating func estimateLatencyAndMount(phone: [VRRotationSample], pods: [VRRotationSample]) {
        let c = configuration
        if let estimate = VRSignalAlignment.estimateLag(
            reference: phone,
            delayed: pods,
            gridStep: c.gridStep,
            lags: c.lags,
            lagStep: c.lagStep
        ), estimate.correlation >= c.minimumCorrelation {
            correlation = estimate.correlation
            if let current = latency {
                latency = current + (estimate.lag - current) * c.estimateSmoothing
            } else {
                latency = estimate.lag
            }
        }
        guard let latency else { return }

        var sources: [SIMD3<Float>] = []
        var targets: [SIMD3<Float>] = []
        var podsCursor = 0
        var phoneCursor = 0
        guard let first = phone.first?.timestamp, let last = phone.last?.timestamp else { return }
        var t = first
        while t <= last {
            if let p = VRSignalAlignment.interpolate(phone, at: t, cursor: &phoneCursor),
               simd_length(p.rate) > c.fitSpeed,
               let a = VRSignalAlignment.interpolate(pods, at: t + latency, cursor: &podsCursor) {
                sources.append(a.rate)
                targets.append(p.rate)
            }
            t += c.gridStep
        }
        guard sources.count >= 30,
              let fit = VRSignalAlignment.fitRotation(from: sources, to: targets),
              fit.confidence >= c.minimumFitConfidence else { return }
        if let current = mountRotation {
            mountRotation = simd_slerp(current, fit.rotation, Float(c.estimateSmoothing)).normalized
        } else {
            mountRotation = fit.rotation
        }
    }

    private func snapshot(_ status: Status, rate: Double?) -> Snapshot {
        Snapshot(
            status: status,
            latency: latency,
            correlation: correlation,
            mountRotationDegrees: mountRotation.map { VRMath.rotationVector(of: $0) * (180 / .pi) },
            residualDegrees: residualDegrees,
            updateRateHz: rate,
            slipCount: slipCount,
            lastSlipTime: lastSlipTime,
            yawBiasTarget: yawBiasTarget
        )
    }

    private static func rate(of samples: [VRRotationSample]) -> Double? {
        guard samples.count >= 2, let first = samples.first, let last = samples.last,
              last.timestamp > first.timestamp else { return nil }
        return Double(samples.count - 1) / (last.timestamp - first.timestamp)
    }

    private static func standardDeviation(_ values: [Float]) -> Float {
        guard values.count > 1 else { return 0 }
        let mean = values.reduce(0, +) / Float(values.count)
        let variance = values.reduce(0) { $0 + ($1 - mean) * ($1 - mean) } / Float(values.count)
        return variance.squareRoot()
    }
}
