import SwiftUI
import MapKit

/// A MapKit map showing a ride's GPS track as a polyline with a colored pin at
/// each detected event. Implemented over UIKit's `MKMapView` (via
/// `UIViewRepresentable`) so it behaves identically on iOS 16+ — SwiftUI's
/// native `Map` polyline support only arrived in iOS 17.
struct RideMapView: UIViewRepresentable {
    let track: [LocationSample]
    let events: [RideEvent]

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
        for event in events {
            guard let lat = event.latitude, let lon = event.longitude else { continue }
            let annotation = EventAnnotation(severity: event.severity)
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
                return view
            }
            return nil
        }
    }
}

/// Map pin for a detected ride event.
final class EventAnnotation: MKPointAnnotation {
    let severity: RideSeverity

    init(severity: RideSeverity) {
        self.severity = severity
        super.init()
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
