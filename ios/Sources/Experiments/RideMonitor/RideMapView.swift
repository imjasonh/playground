import SwiftUI
import MapKit

/// A MapKit map showing a ride's GPS track as speed-colored polylines (same
/// slow/easy/brisk/fast buckets as the Live Activity sparkline) with a colored
/// pin at each of the biggest detected events. Implemented over UIKit's
/// `MKMapView` (via `UIViewRepresentable`) so it behaves identically on iOS 16+
/// — SwiftUI's native `Map` polyline support only arrived in iOS 17.
///
/// Pass the full event list; the map itself caps pins to the biggest hits via
/// `RideMapEventFilter` so saved rides stay readable. Recording is unchanged.
struct RideMapView: UIViewRepresentable {
    let track: [LocationSample]
    let events: [RideEvent]
    /// Max event pins to draw. Crashes always win a slot (see `RideMapEventFilter`).
    var maxMapEvents: Int = RideMapEventFilter.defaultLimit

    func makeCoordinator() -> Coordinator { Coordinator() }

    func makeUIView(context: Context) -> MKMapView {
        let map = MKMapView()
        map.delegate = context.coordinator
        map.isRotateEnabled = false
        map.pointOfInterestFilter = .excludingAll
        return map
    }

    func updateUIView(_ map: MKMapView, context: Context) {
        // SwiftUI can call this often; rebuild only when the ride geometry changes.
        let signature = "\(track.count)|\(track.first?.t ?? -1)|\(track.last?.t ?? -1)|\(events.count)|\(maxMapEvents)"
        guard context.coordinator.lastSignature != signature else { return }
        context.coordinator.lastSignature = signature

        map.removeOverlays(map.overlays)
        map.removeAnnotations(map.annotations)

        let routeSegments = RideMapRouteBuilder.segments(from: track)
        for segment in routeSegments {
            var coords = segment.coordinates
            let polyline = SpeedColoredPolyline(coordinates: &coords, count: coords.count)
            polyline.speedBucket = segment.speedBucket
            map.addOverlay(polyline)
        }

        let coords = routeSegments.flatMap(\.coordinates)
        // Fall back to raw track coords when building the visible rect if the
        // builder produced nothing (e.g. a single fix) but we still have points.
        let fitCoords: [CLLocationCoordinate2D] = {
            if coords.count >= 2 { return coords }
            return track
                .map { CLLocationCoordinate2D(latitude: $0.latitude, longitude: $0.longitude) }
                .filter { CLLocationCoordinate2DIsValid($0) }
        }()

        var annotations: [EventAnnotation] = []
        for event in RideMapEventFilter.selectForMap(events, limit: maxMapEvents) {
            guard let lat = event.latitude, let lon = event.longitude else { continue }
            let annotation = EventAnnotation(severity: event.severity, peakG: event.peakG)
            annotation.coordinate = CLLocationCoordinate2D(latitude: lat, longitude: lon)
            annotation.title = event.severity.title
            annotation.subtitle = String(format: "%.1f g", event.peakG)
            annotations.append(annotation)
        }
        map.addAnnotations(annotations)

        // Start/finish markers for context.
        if let start = fitCoords.first {
            let a = EndpointAnnotation(isStart: true)
            a.coordinate = start
            a.title = "Start"
            map.addAnnotation(a)
        }
        if fitCoords.count >= 2, let end = fitCoords.last {
            let a = EndpointAnnotation(isStart: false)
            a.coordinate = end
            a.title = "Finish"
            map.addAnnotation(a)
        }

        if fitCoords.count >= 2 {
            let rect = MKPolyline(coordinates: fitCoords, count: fitCoords.count).boundingMapRect
            map.setVisibleMapRect(
                rect,
                edgePadding: UIEdgeInsets(top: 40, left: 40, bottom: 40, right: 40),
                animated: false
            )
        } else if let center = fitCoords.first ?? annotations.first?.coordinate {
            map.setRegion(
                MKCoordinateRegion(center: center, latitudinalMeters: 800, longitudinalMeters: 800),
                animated: false
            )
        }
    }

    final class Coordinator: NSObject, MKMapViewDelegate {
        var lastSignature: String?

        func mapView(_ mapView: MKMapView, rendererFor overlay: MKOverlay) -> MKOverlayRenderer {
            guard let polyline = overlay as? MKPolyline else {
                return MKOverlayRenderer(overlay: overlay)
            }
            let renderer = MKPolylineRenderer(polyline: polyline)
            if let colored = polyline as? SpeedColoredPolyline {
                renderer.strokeColor = SpeedColoredPolyline.strokeColor(for: colored.speedBucket)
            } else {
                renderer.strokeColor = .systemBlue
            }
            renderer.lineWidth = 4
            renderer.lineCap = .round
            renderer.lineJoin = .round
            return renderer
        }

        func mapView(_ mapView: MKMapView, viewFor annotation: MKAnnotation) -> MKAnnotationView? {
            if let endpoint = annotation as? EndpointAnnotation {
                let id = "endpoint"
                let view = (mapView.dequeueReusableAnnotationView(withIdentifier: id) as? MKMarkerAnnotationView)
                    ?? MKMarkerAnnotationView(annotation: annotation, reuseIdentifier: id)
                view.annotation = annotation
                view.markerTintColor = endpoint.isStart ? .systemGreen : .darkGray
                view.glyphImage = UIImage(systemName: endpoint.isStart ? "flag" : "flag.checkered")
                view.canShowCallout = true
                view.displayPriority = .required
                return view
            }
            if let event = annotation as? EventAnnotation {
                let id = "event"
                let view = (mapView.dequeueReusableAnnotationView(withIdentifier: id) as? MKMarkerAnnotationView)
                    ?? MKMarkerAnnotationView(annotation: annotation, reuseIdentifier: id)
                view.annotation = annotation
                view.markerTintColor = event.markerColor
                view.glyphImage = UIImage(systemName: event.severity.icon)
                view.canShowCallout = true
                view.displayPriority = event.displayPriority
                return view
            }
            return nil
        }
    }
}

/// Polyline colored by `RideLiveFormatting.speedBucket` (0 slow … 3 fast).
final class SpeedColoredPolyline: MKPolyline {
    /// Set after init — MKPolyline's coordinate initializer is inherited as-is.
    var speedBucket: Int = 0

    /// Matches `RideElevationProfileView` / Live Activity legend colors.
    static func strokeColor(for speedBucket: Int) -> UIColor {
        switch speedBucket {
        case 0: return .systemBlue
        case 1: return .systemGreen
        case 2: return .systemOrange
        default: return .systemRed
        }
    }
}

/// Map pin for a detected ride event.
final class EventAnnotation: MKPointAnnotation {
    let severity: RideSeverity
    let peakG: Double

    init(severity: RideSeverity, peakG: Double) {
        self.severity = severity
        self.peakG = peakG
        super.init()
    }

    /// When the map is zoomed out and pins collide, MapKit hides the
    /// lowest-priority ones first — so harder hits must outrank lighter ones.
    /// Crashes are always shown; everything else scales with its peak g.
    var displayPriority: MKFeatureDisplayPriority {
        Self.displayPriority(severity: severity, peakG: peakG)
    }

    static func displayPriority(severity: RideSeverity, peakG: Double) -> MKFeatureDisplayPriority {
        if severity == .crash { return .required }
        // Map 0–8g onto 500–980, keeping even the hardest non-crash hit below
        // `.required` (1000) so crash pins can never be displaced by it.
        let clamped = min(max(peakG, 0), 8)
        return MKFeatureDisplayPriority(Float(500 + clamped / 8 * 480))
    }

    var markerColor: UIColor {
        switch severity {
        case .shake: return .systemBlue
        case .pothole: return .systemOrange
        case .impact: return .systemRed
        case .crash: return .systemPink
        }
    }
}

/// Map pin for the start/finish of a ride.
final class EndpointAnnotation: MKPointAnnotation {
    let isStart: Bool

    init(isStart: Bool) {
        self.isStart = isStart
        super.init()
    }
}
