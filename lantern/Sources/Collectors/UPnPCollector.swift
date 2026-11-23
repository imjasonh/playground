import Darwin
import Foundation

/// Audits active UPnP Internet Gateway Device (IGD) inbound port forwards on the router.
/// Read-only: uses SSDP M-SEARCH + SOAP `GetGenericPortMappingEntry`.
enum UPnPCollector {
    static let maxEntriesToFetch = 64

    static func collect() async -> [UPnPMapping] {
        let locations = await discoverIGDLocations(timeoutSeconds: 1.5)
        guard !locations.isEmpty else { return [] }

        var allMappings: [UPnPMapping] = []
        var seenIDs: Set<String> = []

        for location in locations {
            guard let url = URL(string: location),
                  let (controlURL, serviceType) = await fetchControlEndpoint(descriptionURL: url)
            else { continue }

            for index in 0..<maxEntriesToFetch {
                guard let mapping = await fetchPortMapping(
                    controlURL: controlURL,
                    serviceType: serviceType,
                    index: index
                ) else {
                    break
                }
                if seenIDs.insert(mapping.id).inserted {
                    allMappings.append(mapping)
                }
            }
        }

        return allMappings.sorted { lhs, rhs in
            if lhs.externalPort != rhs.externalPort { return lhs.externalPort < rhs.externalPort }
            return lhs.protocolName < rhs.protocolName
        }
    }

    // MARK: - Pure parsers (unit-tested)

    /// Extracts `LOCATION:` URLs from one or more SSDP HTTP responses.
    static func parseSSDPLocations(_ rawResponse: String) -> [String] {
        var results: [String] = []
        var seen: Set<String> = []
        for rawLine in rawResponse.components(separatedBy: .newlines) {
            let line = rawLine.trimmingCharacters(in: .whitespacesAndNewlines)
            if line.lowercased().hasPrefix("location:") {
                let value = String(line.dropFirst("location:".count))
                    .trimmingCharacters(in: .whitespaces)
                if !value.isEmpty, seen.insert(value).inserted {
                    results.append(value)
                }
            }
        }
        return results
    }

    /// Parses a router's UPnP root description XML to find WANIPConnection or WANPPPConnection.
    static func parseControlEndpoint(
        xml: String,
        baseURL: URL
    ) -> (controlURL: URL, serviceType: String)? {
        let targets = [
            "urn:schemas-upnp-org:service:WANIPConnection:2",
            "urn:schemas-upnp-org:service:WANIPConnection:1",
            "urn:schemas-upnp-org:service:WANPPPConnection:1",
        ]
        // Walk <service>...</service> blocks.
        let blocks = xml.components(separatedBy: "<service>")
        for block in blocks.dropFirst() {
            guard let endIdx = block.range(of: "</service>")?.lowerBound else { continue }
            let serviceXML = String(block[..<endIdx])
            guard let serviceType = xmlTagValue("serviceType", in: serviceXML),
                  targets.contains(serviceType),
                  let controlPath = xmlTagValue("controlURL", in: serviceXML),
                  let resolved = URL(string: controlPath, relativeTo: baseURL)?.absoluteURL
            else { continue }
            return (resolved, serviceType)
        }
        return nil
    }

    /// Parses a SOAP `GetGenericPortMappingEntryResponse` body into a `UPnPMapping`.
    static func parsePortMappingSOAP(_ xml: String) -> UPnPMapping? {
        guard let extStr = xmlTagValue("NewExternalPort", in: xml),
              let extPort = UInt16(extStr),
              let intStr = xmlTagValue("NewInternalPort", in: xml),
              let intPort = UInt16(intStr),
              let client = xmlTagValue("NewInternalClient", in: xml),
              !client.isEmpty
        else { return nil }

        let proto = xmlTagValue("NewProtocol", in: xml)?.uppercased() ?? "TCP"
        let desc = xmlTagValue("NewPortMappingDescription", in: xml) ?? ""
        let enabledRaw = xmlTagValue("NewEnabled", in: xml)?.lowercased() ?? "1"
        let enabled = enabledRaw == "1" || enabledRaw == "true"
        let lease = Int(xmlTagValue("NewLeaseDuration", in: xml) ?? "0") ?? 0

        return UPnPMapping(
            externalPort: extPort,
            internalPort: intPort,
            internalClient: client,
            protocolName: proto,
            description: desc,
            enabled: enabled,
            leaseDuration: lease
        )
    }

    static func xmlTagValue(_ tag: String, in xml: String) -> String? {
        let open = "<\(tag)>"
        let close = "</\(tag)>"
        guard let startRange = xml.range(of: open),
              let endRange = xml.range(of: close, range: startRange.upperBound..<xml.endIndex)
        else { return nil }
        return String(xml[startRange.upperBound..<endRange.lowerBound])
            .trimmingCharacters(in: .whitespacesAndNewlines)
    }

    // MARK: - Network I/O

    private static func discoverIGDLocations(timeoutSeconds: TimeInterval) async -> [String] {
        await Task.detached(priority: .utility) {
            let fd = socket(AF_INET, SOCK_DGRAM, IPPROTO_UDP)
            guard fd >= 0 else { return [] }
            defer { close(fd) }

            var tv = timeval(
                tv_sec: Int(timeoutSeconds),
                tv_usec: Int32((timeoutSeconds - floor(timeoutSeconds)) * 1_000_000)
            )
            setsockopt(fd, SOL_SOCKET, SO_RCVTIMEO, &tv, socklen_t(MemoryLayout<timeval>.size))

            let searchPayload = [
                "M-SEARCH * HTTP/1.1",
                "HOST: 239.255.255.250:1900",
                "MAN: \"ssdp:discover\"",
                "MX: 1",
                "ST: urn:schemas-upnp-org:device:InternetGatewayDevice:1",
                "",
                "",
            ].joined(separator: "\r\n")

            var dest = sockaddr_in()
            dest.sin_len = UInt8(MemoryLayout<sockaddr_in>.size)
            dest.sin_family = sa_family_t(AF_INET)
            dest.sin_port = UInt16(1900).bigEndian
            guard inet_pton(AF_INET, "239.255.255.250", &dest.sin_addr) == 1 else { return [] }

            let bytes = Array(searchPayload.utf8)
            _ = bytes.withUnsafeBytes { buf in
                withUnsafePointer(to: &dest) { ptr in
                    ptr.withMemoryRebound(to: sockaddr.self, capacity: 1) { sockPtr in
                        sendto(
                            fd,
                            buf.baseAddress,
                            buf.count,
                            0,
                            sockPtr,
                            socklen_t(MemoryLayout<sockaddr_in>.size)
                        )
                    }
                }
            }

            var combined = ""
            var buffer = [UInt8](repeating: 0, count: 4096)
            let deadline = Date().addingTimeInterval(timeoutSeconds)
            while Date() < deadline {
                let n = recv(fd, &buffer, buffer.count, 0)
                if n <= 0 { break }
                if let text = String(bytes: buffer[0..<n], encoding: .utf8) {
                    combined.append(text)
                    combined.append("\n")
                }
            }
            return parseSSDPLocations(combined)
        }.value
    }

    private static func fetchControlEndpoint(
        descriptionURL: URL
    ) async -> (controlURL: URL, serviceType: String)? {
        var req = URLRequest(url: descriptionURL, timeoutInterval: 3)
        req.httpMethod = "GET"
        guard let (data, resp) = try? await URLSession.shared.data(for: req),
              let http = resp as? HTTPURLResponse,
              (200...299).contains(http.statusCode),
              let xml = String(data: data, encoding: .utf8)
        else { return nil }
        return parseControlEndpoint(xml: xml, baseURL: descriptionURL)
    }

    private static func fetchPortMapping(
        controlURL: URL,
        serviceType: String,
        index: Int
    ) async -> UPnPMapping? {
        let soap = """
        <?xml version="1.0"?>
        <s:Envelope xmlns:s="http://schemas.xmlsoap.org/soap/envelope/" s:encodingStyle="http://schemas.xmlsoap.org/soap/encoding/">
          <s:Body>
            <u:GetGenericPortMappingEntry xmlns:u="\(serviceType)">
              <NewPortMappingIndex>\(index)</NewPortMappingIndex>
            </u:GetGenericPortMappingEntry>
          </s:Body>
        </s:Envelope>
        """
        var req = URLRequest(url: controlURL, timeoutInterval: 3)
        req.httpMethod = "POST"
        req.setValue("text/xml; charset=\"utf-8\"", forHTTPHeaderField: "Content-Type")
        req.setValue("\"\(serviceType)#GetGenericPortMappingEntry\"", forHTTPHeaderField: "SOAPACTION")
        req.httpBody = Data(soap.utf8)

        guard let (data, resp) = try? await URLSession.shared.data(for: req),
              let http = resp as? HTTPURLResponse,
              (200...299).contains(http.statusCode),
              let xml = String(data: data, encoding: .utf8)
        else { return nil }
        return parsePortMappingSOAP(xml)
    }
}
