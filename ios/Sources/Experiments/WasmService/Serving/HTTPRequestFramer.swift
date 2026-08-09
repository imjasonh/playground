import Foundation

/// Decides when the bytes read off a socket add up to exactly one HTTP/1.1
/// request.
///
/// The guest is handed raw request bytes, so the host's only job at this layer
/// is framing: find the end of the headers, work out how much body follows,
/// and refuse anything it cannot frame honestly. It deliberately does not
/// interpret the request — no routing, no header rewriting — because that is
/// the guest's business.
///
/// Pure, and separately tested: everything hard about a socket server lives in
/// this function, and none of it needs a socket to check.
enum HTTPRequestFramer {
    enum Outcome: Equatable {
        /// The request is not all here yet.
        case needMore
        /// A complete request occupies the first `byteCount` bytes.
        case complete(byteCount: Int)
        /// Nothing valid can come of this; answer with `status` and hang up.
        case refuse(status: Int, reason: String)
    }

    /// Headers alone are never legitimately this large, and a client that
    /// never sends the blank line would otherwise buffer forever.
    static let maximumHeaderBytes = 64 * 1024

    static func examine(_ buffer: Data, maximumBodyBytes: Int) -> Outcome {
        guard let headerEnd = terminatorOffset(in: buffer) else {
            if buffer.count > maximumHeaderBytes {
                return .refuse(status: 431, reason: "request headers are too large")
            }
            return .needMore
        }

        let headerBytes = headerEnd + 4
        let head = String(decoding: buffer.prefix(headerEnd), as: UTF8.self)
        let headers = parseHeaders(head)

        // Chunked bodies would need de-chunking before the guest could parse
        // the request, and nothing that talks to this sends them. Say so
        // rather than silently handing the guest a body it cannot read.
        if headers["transfer-encoding"] != nil {
            return .refuse(status: 501, reason: "chunked requests are not supported")
        }

        guard let rawLength = headers["content-length"] else {
            return .complete(byteCount: headerBytes)
        }
        guard let contentLength = Int(rawLength.trimmingCharacters(in: .whitespaces)), contentLength >= 0 else {
            return .refuse(status: 400, reason: "Content-Length is not a number")
        }
        guard contentLength <= maximumBodyBytes else {
            return .refuse(status: 413, reason: "request body is larger than \(maximumBodyBytes) bytes")
        }

        let total = headerBytes + contentLength
        return buffer.count >= total ? .complete(byteCount: total) : .needMore
    }

    /// How many bytes precede the blank line that ends the headers.
    ///
    /// Counted from the buffer's own start index rather than assuming zero:
    /// `Data` sliced off a connection keeps the indices of its parent.
    static func terminatorOffset(in buffer: Data) -> Int? {
        guard let range = buffer.range(of: Data("\r\n\r\n".utf8)) else { return nil }
        return buffer.distance(from: buffer.startIndex, to: range.lowerBound)
    }

    static func parseHeaders(_ head: String) -> [String: String] {
        var headers: [String: String] = [:]
        for line in head.components(separatedBy: "\r\n").dropFirst() where !line.isEmpty {
            guard let colon = line.firstIndex(of: ":") else { continue }
            let name = line[..<colon].trimmingCharacters(in: .whitespaces).lowercased()
            let value = line[line.index(after: colon)...].trimmingCharacters(in: .whitespaces)
            headers[name] = value
        }
        return headers
    }

    /// A complete response for a request the host refused, since a refusal
    /// still has to leave the socket with something to read.
    static func refusal(status: Int, reason: String) -> Data {
        let body = reason + "\n"
        var response = "HTTP/1.1 \(status) \(reasonPhrase(status))\r\n"
        response += "Content-Type: text/plain; charset=utf-8\r\n"
        response += "Content-Length: \(body.utf8.count)\r\n"
        response += "Connection: close\r\n\r\n"
        response += body
        return Data(response.utf8)
    }

    static func reasonPhrase(_ status: Int) -> String {
        switch status {
        case 400: return "Bad Request"
        case 413: return "Content Too Large"
        case 431: return "Request Header Fields Too Large"
        case 500: return "Internal Server Error"
        case 501: return "Not Implemented"
        case 503: return "Service Unavailable"
        default: return "Status"
        }
    }
}
