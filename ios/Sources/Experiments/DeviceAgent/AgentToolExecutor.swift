import Contacts
import CoreLocation
import EventKit
import Foundation
import MapKit
import UIKit

/// Shared mutable state tools read and write (attachments, browser URL, drafts).
@MainActor
final class AgentToolContext: ObservableObject {
    let inbox: AgentInbox
    let permissions: AgentPermissionGate

    @Published var mode: AgentMode = .act
    @Published var browserURL: URL?
    @Published var browserTitle: String = ""
    @Published var pendingSMS: AgentSMSDraft?
    @Published var pendingMail: AgentMailDraft?
    @Published var pendingConfirmation: AgentConfirmationRequest?
    @Published var lastToolLog: [(name: String, detail: String)] = []

    private var confirmationContinuation: CheckedContinuation<Bool, Never>?
    private let locationManager = CLLocationManager()

    init() {
        self.inbox = AgentInbox.shared
        self.permissions = AgentPermissionGate.shared
    }

    init(inbox: AgentInbox, permissions: AgentPermissionGate = AgentPermissionGate.shared) {
        self.inbox = inbox
        self.permissions = permissions
    }

    func logTool(name: String, detail: String) {
        lastToolLog.append((name, detail))
        if lastToolLog.count > 50 {
            lastToolLog.removeFirst(lastToolLog.count - 50)
        }
    }

    func confirmWrites(title: String, message: String) async -> Bool {
        if pendingConfirmation != nil {
            // Resolve any stale waiter.
            confirmationContinuation?.resume(returning: false)
            confirmationContinuation = nil
        }
        let request = AgentConfirmationRequest(title: title, message: message)
        pendingConfirmation = request
        let ok = await withCheckedContinuation { (cont: CheckedContinuation<Bool, Never>) in
            confirmationContinuation = cont
        }
        pendingConfirmation = nil
        return ok
    }

    func resolveConfirmation(_ allowed: Bool) {
        confirmationContinuation?.resume(returning: allowed)
        confirmationContinuation = nil
        pendingConfirmation = nil
    }

    func currentLocation() async throws -> CLLocation {
        try await permissions.ensure(.location)
        return try await withCheckedThrowingContinuation { cont in
            let delegate = OneShotLocationDelegate(manager: locationManager) { result in
                cont.resume(with: result)
            }
            OneShotLocationDelegate.retain(delegate)
            locationManager.delegate = delegate
            locationManager.desiredAccuracy = kCLLocationAccuracyHundredMeters
            locationManager.requestLocation()
        }
    }
}

struct AgentSMSDraft: Equatable {
    var recipients: [String]
    var body: String
}

struct AgentMailDraft: Equatable {
    var to: [String]
    var subject: String
    var body: String
}

/// Single-fix location fix used by the location tool.
private final class OneShotLocationDelegate: NSObject, CLLocationManagerDelegate {
    private static var retained: [ObjectIdentifier: OneShotLocationDelegate] = [:]

    private let manager: CLLocationManager
    private let completion: (Result<CLLocation, Error>) -> Void
    private var finished = false

    init(manager: CLLocationManager, completion: @escaping (Result<CLLocation, Error>) -> Void) {
        self.manager = manager
        self.completion = completion
    }

    static func retain(_ delegate: OneShotLocationDelegate) {
        retained[ObjectIdentifier(delegate)] = delegate
    }

    private func finish(_ result: Result<CLLocation, Error>) {
        guard !finished else { return }
        finished = true
        manager.delegate = nil
        Self.retained[ObjectIdentifier(self)] = nil
        completion(result)
    }

    func locationManager(_ manager: CLLocationManager, didUpdateLocations locations: [CLLocation]) {
        if let location = locations.last {
            finish(.success(location))
        } else {
            finish(.failure(AgentToolError.unavailable("No location fix.")))
        }
    }

    func locationManager(_ manager: CLLocationManager, didFailWithError error: Error) {
        finish(.failure(error))
    }
}

/// Concrete tool implementations used by Foundation Models tool wrappers.
@MainActor
enum AgentToolExecutor {
    static func listAttachments(context: AgentToolContext) -> String {
        context.inbox.reloadAttachments()
        let items = context.inbox.attachments
        context.logTool(name: "listAttachments", detail: "\(items.count) file(s)")
        guard !items.isEmpty else {
            return "No attachments in the Device Agent inbox. Share a file via the Run Device Agent Shortcut or attach one in the app."
        }
        return items.map { att in
            "- \(att.filename) (\(att.byteCount) bytes, id=\(att.id.uuidString.prefix(8)))"
        }.joined(separator: "\n")
    }

    static func readTextAttachment(context: AgentToolContext, filenameQuery: String) throws -> String {
        context.inbox.reloadAttachments()
        let query = filenameQuery.trimmingCharacters(in: .whitespacesAndNewlines)
        guard let attachment = context.inbox.attachments.first(where: {
            $0.filename.localizedCaseInsensitiveContains(query) || $0.id.uuidString.localizedCaseInsensitiveContains(query)
        }) else {
            throw AgentToolError.invalidArguments("No attachment matching “\(filenameQuery)”.")
        }
        guard let url = context.inbox.fileURL(for: attachment) else {
            throw AgentToolError.unavailable("Attachment file is missing on disk.")
        }
        let data = try Data(contentsOf: url)
        context.logTool(name: "readTextAttachment", detail: attachment.filename)
        if let text = String(data: data, encoding: .utf8) ?? String(data: data, encoding: .isoLatin1) {
            let clipped = text.count > 8_000 ? String(text.prefix(8_000)) + "\n…" : text
            return "File \(attachment.filename):\n\(clipped)"
        }
        return "File \(attachment.filename) is \(data.count) bytes of non-text data (UTI \(attachment.utTypeIdentifier ?? "unknown"))."
    }

    static func getCurrentDateTime() -> String {
        let formatter = DateFormatter()
        formatter.dateStyle = .full
        formatter.timeStyle = .medium
        return formatter.string(from: Date())
    }

    static func openURL(_ raw: String) throws -> String {
        let trimmed = raw.trimmingCharacters(in: .whitespacesAndNewlines)
        guard let url = URL(string: trimmed), url.scheme != nil else {
            throw AgentToolError.invalidArguments("Need an absolute URL with a scheme.")
        }
        UIApplication.shared.open(url)
        return "Opened \(url.absoluteString)"
    }

    static func searchContacts(context: AgentToolContext, query: String) async throws -> String {
        try await context.permissions.ensure(.contacts)
        let store = CNContactStore()
        let keys: [CNKeyDescriptor] = [
            CNContactGivenNameKey as CNKeyDescriptor,
            CNContactFamilyNameKey as CNKeyDescriptor,
            CNContactNicknameKey as CNKeyDescriptor,
            CNContactPhoneNumbersKey as CNKeyDescriptor,
            CNContactEmailAddressesKey as CNKeyDescriptor,
        ]
        let request = CNContactFetchRequest(keysToFetch: keys)
        var matches: [String] = []
        let needle = query.trimmingCharacters(in: .whitespacesAndNewlines).lowercased()
        try store.enumerateContacts(with: request) { contact, stop in
            let name = [contact.givenName, contact.familyName]
                .filter { !$0.isEmpty }
                .joined(separator: " ")
            let nick = contact.nickname
            let hay = "\(name) \(nick)".lowercased()
            guard hay.contains(needle) || needle.isEmpty else { return }
            let phones = contact.phoneNumbers.prefix(2).map(\.value.stringValue).joined(separator: ", ")
            let emails = contact.emailAddresses.prefix(2).map { $0.value as String }.joined(separator: ", ")
            var line = name.isEmpty ? "(unnamed)" : name
            if !phones.isEmpty { line += " | phone: \(phones)" }
            if !emails.isEmpty { line += " | email: \(emails)" }
            matches.append(line)
            if matches.count >= 8 { stop.pointee = true }
        }
        context.logTool(name: "searchContacts", detail: query)
        if matches.isEmpty {
            return "No contacts matched “\(query)”."
        }
        return matches.joined(separator: "\n")
    }

    static func getCurrentLocation(context: AgentToolContext) async throws -> String {
        let location = try await context.currentLocation()
        context.logTool(name: "getCurrentLocation", detail: "fix")
        let geocoder = CLGeocoder()
        let placemarks = try? await geocoder.reverseGeocodeLocation(location)
        let place = placemarks?.first
        let placeLine = [place?.name, place?.locality, place?.administrativeArea]
            .compactMap { $0 }
            .filter { !$0.isEmpty }
            .joined(separator: ", ")
        var lines = [
            String(format: "lat=%.5f lon=%.5f", location.coordinate.latitude, location.coordinate.longitude),
            String(format: "horizontalAccuracy=%.0fm", location.horizontalAccuracy),
        ]
        if !placeLine.isEmpty {
            lines.insert(placeLine, at: 0)
        }
        return lines.joined(separator: "\n")
    }

    static func openMapsDirections(query: String) throws -> String {
        let trimmed = query.trimmingCharacters(in: .whitespacesAndNewlines)
        guard !trimmed.isEmpty else {
            throw AgentToolError.invalidArguments("Need a destination query.")
        }
        var components = URLComponents(string: "http://maps.apple.com/")
        components?.queryItems = [
            URLQueryItem(name: "daddr", value: trimmed),
            URLQueryItem(name: "dirflg", value: "d"),
        ]
        guard let url = components?.url else {
            throw AgentToolError.invalidArguments("Could not build Maps URL.")
        }
        UIApplication.shared.open(url)
        return "Opened Maps directions to \(trimmed)"
    }

    static func createCalendarEvent(
        context: AgentToolContext,
        title: String,
        notes: String,
        hoursFromNow: Double
    ) async throws -> String {
        guard context.mode == .act else {
            throw AgentToolError.unavailable("Switch to Act mode to create calendar events.")
        }
        try await context.permissions.ensure(.calendars)
        let start = Date().addingTimeInterval(hoursFromNow * 3600)
        let end = start.addingTimeInterval(3600)
        let formatter = DateFormatter()
        formatter.dateStyle = .medium
        formatter.timeStyle = .short
        let summary = "Create event “\(title)” at \(formatter.string(from: start))"
        let allowed = await context.confirmWrites(title: "Create calendar event?", message: summary)
        guard allowed else { throw AgentToolError.confirmationRejected }

        let store = EKEventStore()
        let event = EKEvent(eventStore: store)
        event.title = title
        event.notes = notes.isEmpty ? nil : notes
        event.startDate = start
        event.endDate = end
        event.calendar = store.defaultCalendarForNewEvents
        try store.save(event, span: .thisEvent)
        context.logTool(name: "createCalendarEvent", detail: title)
        return "Created event “\(title)” at \(formatter.string(from: start))."
    }

    static func draftSMS(context: AgentToolContext, recipients: String, body: String) async throws -> String {
        guard context.mode == .act else {
            throw AgentToolError.unavailable("Switch to Act mode to draft messages.")
        }
        let numbers = recipients.split(separator: ",")
            .map { $0.trimmingCharacters(in: .whitespacesAndNewlines) }
            .filter { !$0.isEmpty }
        guard !numbers.isEmpty else {
            throw AgentToolError.invalidArguments("Need at least one recipient phone number.")
        }
        let allowed = await context.confirmWrites(
            title: "Open Messages draft?",
            message: "To: \(numbers.joined(separator: ", "))\n\n\(body)"
        )
        guard allowed else { throw AgentToolError.confirmationRejected }
        context.pendingSMS = AgentSMSDraft(recipients: numbers, body: body)
        context.logTool(name: "draftSMS", detail: numbers.joined(separator: ","))
        return "Opening Messages composer."
    }

    static func draftEmail(context: AgentToolContext, to: String, subject: String, body: String) async throws -> String {
        guard context.mode == .act else {
            throw AgentToolError.unavailable("Switch to Act mode to draft email.")
        }
        let addresses = to.split(separator: ",")
            .map { $0.trimmingCharacters(in: .whitespacesAndNewlines) }
            .filter { !$0.isEmpty }
        guard !addresses.isEmpty else {
            throw AgentToolError.invalidArguments("Need at least one email address.")
        }
        let allowed = await context.confirmWrites(
            title: "Open Mail draft?",
            message: "To: \(addresses.joined(separator: ", "))\nSubject: \(subject)\n\n\(body)"
        )
        guard allowed else { throw AgentToolError.confirmationRejected }
        context.pendingMail = AgentMailDraft(to: addresses, subject: subject, body: body)
        context.logTool(name: "draftEmail", detail: addresses.joined(separator: ","))
        return "Opening Mail composer."
    }

    static func browserLoadDemo(context: AgentToolContext) -> String {
        guard context.mode == .browse || context.mode == .act else {
            return "Switch to Browse (or Act) mode to use the in-app browser demo."
        }
        if let url = Bundle.main.url(forResource: "DeviceAgentDemoMail", withExtension: "html") {
            context.browserURL = url
            context.browserTitle = "Demo Mail"
            context.logTool(name: "browserLoadDemo", detail: url.lastPathComponent)
            return "Loaded bundled Demo Mail page in the in-app browser."
        }
        // Fallback: data URL so the tool still works if the resource is missing.
        let html = DeviceAgentDemoHTML.fallback
        let encoded = Data(html.utf8).base64EncodedString()
        context.browserURL = URL(string: "data:text/html;base64,\(encoded)")
        context.browserTitle = "Demo Mail"
        context.logTool(name: "browserLoadDemo", detail: "data-url")
        return "Loaded Demo Mail (inline fallback) in the in-app browser."
    }

    static func browserRead(context: AgentToolContext) -> String {
        let title = context.browserTitle.isEmpty ? "(none)" : context.browserTitle
        let url = context.browserURL?.absoluteString ?? "(no page loaded)"
        return "Browser title: \(title)\nURL: \(url)"
    }

    static func helpText(mode: AgentMode) -> String {
        """
        Device Agent can use tools for attachments, contacts, location, Maps, calendar (with confirm), \
        SMS/Mail drafts (with confirm), and a bundled browser demo. Mode is \(mode.title). \
        Permissions are requested only when a tool needs them. Requires Apple Intelligence \
        (on-device Foundation Models) on this device.
        """
    }
}

enum DeviceAgentDemoHTML {
    static let fallback = """
    <!doctype html>
    <html lang="en">
    <meta charset="utf-8"/>
    <meta name="viewport" content="width=device-width, initial-scale=1"/>
    <title>Demo Mail</title>
    <style>
      body{font-family:-apple-system,sans-serif;margin:16px;background:#f4f4f5;color:#111}
      h1{font-size:1.25rem}
      label{display:block;margin:.75rem 0 .25rem;font-size:.85rem;color:#555}
      input,textarea{width:100%;box-sizing:border-box;padding:.6rem;border:1px solid #ccc;border-radius:8px;font:inherit}
      textarea{min-height:120px}
      button{margin-top:1rem;padding:.7rem 1rem;border:0;border-radius:10px;background:#0b57d0;color:#fff;font:inherit}
      .sent{display:none;margin-top:1rem;padding:.75rem;background:#e6f4ea;border-radius:8px}
    </style>
    <h1>Demo Mail</h1>
    <p>First-party page for browser tools — not Gmail.</p>
    <label>To</label>
    <input id="to" value="mom@example.com"/>
    <label>Subject</label>
    <input id="subject" value="Running late"/>
    <label>Body</label>
    <textarea id="body">On my way — ETA soon.</textarea>
    <button id="send" type="button">Send</button>
    <div class="sent" id="sent">Queued locally (demo only).</div>
    <script>
      document.getElementById('send').onclick=()=>{
        document.getElementById('sent').style.display='block';
        document.title='Demo Mail — sent';
      };
    </script>
    </html>
    """
}
