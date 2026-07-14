import SwiftUI
import MapKit

/// A MapKit map showing a ride's GPS track as a polyline with a colored pin at
/// each detected event. Implemented over UIKit's `MKMapView` (via
/// `UIViewRepresentable`) so it behaves identically on iOS 16+ — SwiftUI's
/// native `Map` polyline support only arrived in iOS 17.
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
        map.removeOverlays(map.overlays)
        map.removeAnnotations(map.annotations)

        let coords = track
            .map { CLLocationCoordinate2D(latitude: $0.latitude, longitude: $0.longitude) }
            .filter { CLLocationCoordinate2DIsValid($0) }

        if coords.count >= 2 {
            map.addOverlay(MKPolyline(coordinates: coords, count: coords.count))
        }

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
        if let start = coords.first {
            let a = EndpointAnnotation(isStart: true)
            a.coordinate = start
            a.title = "Start"
            map.addAnnotation(a)
        }
        if coords.count >= 2, let end = coords.last {
            let a = EndpointAnnotation(isStart: false)
            a.coordinate = end
            a.title = "Finish"
            map.addAnnotation(a)
        }

        if coords.count >= 2 {
            let rect = MKPolyline(coordinates: coords, count: coords.count).boundingMapRect
            map.setVisibleMapRect(
                rect,
                edgePadding: UIEdgeInsets(top: 40, left: 40, bottom: 40, right: 40),
                animated: false
            )
        } else if let center = coords.first ?? annotations.first?.coordinate {
            map.setRegion(
                MKCoordinateRegion(center: center, latitudinalMeters: 800, longitudinalMeters: 800),
                animated: false
            )
        }
    }

    final class Coordinator: NSObject, MKMapViewDelegate {
        func mapView(_ mapView: MKMapView, rendererFor overlay: MKOverlay) -> MKOverlayRenderer {
            guard let polyline = overlay as? MKPolyline else {
                return MKOverlayRenderer(overlay: overlay)
            }
            let renderer = MKPolylineRenderer(polyline: polyline)
            renderer.strokeColor = .systemBlue
            renderer.lineWidth = 4
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
