//! SSRF hardening: decide whether a user-supplied URL is safe to fetch.
//!
//! A CORS proxy fetches arbitrary user-supplied URLs server-side, which makes a
//! naive implementation a Server-Side Request Forgery engine: an attacker can
//! point it at `http://127.0.0.1`, RFC1918 space, or a cloud metadata endpoint
//! (`169.254.169.254`) and have your infrastructure make the request for them.
//!
//! This module rejects those targets up front. It:
//!
//! * allows only the `http` and `https` schemes;
//! * blocks literal IP hosts in loopback, private, link-local, CGNAT,
//!   benchmarking, documentation, and reserved ranges (IPv4 and IPv6,
//!   including IPv4-mapped/compatible IPv6);
//! * blocks hostnames that name the local machine or a metadata service
//!   (`localhost`, `*.local`, `*.internal`, `metadata.google.internal`, ...).
//!
//! ## Known limitation: DNS rebinding
//!
//! The Cloudflare Workers runtime does not expose DNS resolution to user code —
//! `fetch` resolves names internally — so this guard cannot resolve a hostname,
//! validate the resulting IP, and pin the connection to it. A hostname that
//! resolves to a private address (the classic `localtest.me` → `127.0.0.1`
//! trick, or a TOCTOU rebind between check and fetch) is therefore **not**
//! caught here by IP range checks. Two things mitigate this in practice:
//! Cloudflare's edge does not route `fetch` to RFC1918/loopback space, and
//! redirects are re-validated hop by hop (see `worker_entry`). If you deploy
//! somewhere that *can* reach a private network, add a resolve-and-pin step.

use std::net::{IpAddr, Ipv4Addr, Ipv6Addr};

use url::{Host, Url};

use crate::error::GuardError;

/// Hostnames that always refer to the local host or an internal metadata
/// service and must never be proxied, regardless of DNS.
const BLOCKED_EXACT_HOSTS: &[&str] = &["localhost", "metadata.google.internal", "metadata.goog"];

/// Suffixes that denote local or internal namespaces.
const BLOCKED_HOST_SUFFIXES: &[&str] = &[".localhost", ".local", ".internal", ".home.arpa"];

/// Parse and validate a raw target string, returning the parsed [`Url`] when it
/// is safe to fetch.
pub fn validate(raw: &str) -> Result<Url, GuardError> {
    let trimmed = raw.trim();
    if trimmed.is_empty() {
        return Err(GuardError::MissingTarget);
    }
    let url = Url::parse(trimmed).map_err(|_| GuardError::InvalidUrl)?;
    validate_url(&url)?;
    Ok(url)
}

/// Validate an already-parsed URL. Used both for the initial target and for
/// each `Location` header while following redirects.
pub fn validate_url(url: &Url) -> Result<(), GuardError> {
    match url.scheme() {
        "http" | "https" => {}
        other => return Err(GuardError::UnsupportedScheme(other.to_string())),
    }
    match url.host() {
        None => Err(GuardError::MissingHost),
        Some(Host::Domain(domain)) => check_domain(domain),
        Some(Host::Ipv4(ip)) => check_ip(IpAddr::V4(ip)),
        Some(Host::Ipv6(ip)) => check_ip(IpAddr::V6(ip)),
    }
}

fn check_domain(domain: &str) -> Result<(), GuardError> {
    let host = domain.to_ascii_lowercase();
    if host.is_empty() {
        return Err(GuardError::MissingHost);
    }
    if BLOCKED_EXACT_HOSTS.contains(&host.as_str())
        || BLOCKED_HOST_SUFFIXES
            .iter()
            .any(|suffix| host.ends_with(suffix))
    {
        return Err(GuardError::BlockedHost(host));
    }
    Ok(())
}

fn check_ip(ip: IpAddr) -> Result<(), GuardError> {
    let blocked = match ip {
        IpAddr::V4(v4) => ipv4_blocked(v4),
        IpAddr::V6(v6) => ipv6_blocked(v6),
    };
    if blocked {
        Err(GuardError::BlockedIp(ip.to_string()))
    } else {
        Ok(())
    }
}

/// Whether an IPv4 address falls in a range the proxy must not reach.
fn ipv4_blocked(ip: Ipv4Addr) -> bool {
    let [a, b, _, _] = ip.octets();
    ip.is_unspecified()          // 0.0.0.0
        || ip.is_loopback()      // 127.0.0.0/8
        || ip.is_private()       // 10/8, 172.16/12, 192.168/16
        || ip.is_link_local()    // 169.254.0.0/16 (incl. cloud metadata)
        || ip.is_broadcast()     // 255.255.255.255
        || ip.is_documentation() // 192.0.2/24, 198.51.100/24, 203.0.113/24
        || ip.is_multicast()     // 224.0.0.0/4
        || a == 0                // 0.0.0.0/8 "this network"
        || (a == 100 && (b & 0xc0) == 64)   // 100.64.0.0/10 CGNAT
        || (a == 198 && (b & 0xfe) == 18)   // 198.18.0.0/15 benchmarking
        || (a == 192 && b == 0 && ip.octets()[2] == 0) // 192.0.0.0/24 IETF
        || a >= 240 // 240.0.0.0/4 reserved
}

/// Whether an IPv6 address falls in a range the proxy must not reach.
fn ipv6_blocked(ip: Ipv6Addr) -> bool {
    // Unwrap IPv4-mapped (::ffff:a.b.c.d) and the deprecated IPv4-compatible
    // form (::a.b.c.d) and apply the IPv4 rules. `to_ipv4` matches any address
    // in ::/96, all of which are non-global, so treating them as IPv4 is safe.
    if let Some(v4) = ip.to_ipv4_mapped() {
        return ipv4_blocked(v4);
    }
    if let Some(v4) = ip.to_ipv4() {
        return ipv4_blocked(v4);
    }
    // Transition mechanisms embed an IPv4 address that the network may route to.
    // Validate the embedded address so e.g. a 6to4/NAT64 wrapper for 127.0.0.1
    // or 169.254.169.254 can't smuggle past the checks below.
    if let Some(v4) = embedded_ipv4(ip) {
        return ipv4_blocked(v4);
    }
    let seg = ip.segments();
    ip.is_unspecified()                 // ::
        || ip.is_loopback()             // ::1
        || ip.is_multicast()            // ff00::/8
        || (seg[0] & 0xffc0) == 0xfe80  // fe80::/10 link-local
        || (seg[0] & 0xfe00) == 0xfc00  // fc00::/7 unique local
        || (seg[0] == 0x2001 && seg[1] == 0x0db8) // 2001:db8::/32 documentation
}

/// Extract the IPv4 address embedded by a transition mechanism, if any:
/// 6to4 (`2002::/16`) or well-known NAT64 (`64:ff9b::/96`).
fn embedded_ipv4(ip: Ipv6Addr) -> Option<Ipv4Addr> {
    let seg = ip.segments();
    // 6to4: 2002:AABB:CCDD::/48 carries the IPv4 A.B.C.D in segments 1 and 2.
    if seg[0] == 0x2002 {
        return Some(Ipv4Addr::new(
            (seg[1] >> 8) as u8,
            (seg[1] & 0xff) as u8,
            (seg[2] >> 8) as u8,
            (seg[2] & 0xff) as u8,
        ));
    }
    // NAT64 well-known prefix 64:ff9b::/96 carries the IPv4 in the last 32 bits.
    if seg[0] == 0x0064
        && seg[1] == 0xff9b
        && seg[2] == 0
        && seg[3] == 0
        && seg[4] == 0
        && seg[5] == 0
    {
        return Some(Ipv4Addr::new(
            (seg[6] >> 8) as u8,
            (seg[6] & 0xff) as u8,
            (seg[7] >> 8) as u8,
            (seg[7] & 0xff) as u8,
        ));
    }
    None
}

#[cfg(test)]
mod tests {
    use super::*;

    fn err(raw: &str) -> GuardError {
        validate(raw).unwrap_err()
    }

    #[test]
    fn allows_public_http_and_https() {
        assert!(validate("http://example.com/").is_ok());
        assert!(validate("https://example.com/path?q=1").is_ok());
        assert!(validate("https://8.8.8.8/").is_ok());
        assert!(validate("https://1.1.1.1").is_ok());
        assert!(validate("http://[2606:4700:4700::1111]/").is_ok());
    }

    #[test]
    fn rejects_missing_and_malformed() {
        assert_eq!(err(""), GuardError::MissingTarget);
        assert_eq!(err("   "), GuardError::MissingTarget);
        assert_eq!(err("not a url"), GuardError::InvalidUrl);
        assert_eq!(err("/relative/path"), GuardError::InvalidUrl);
    }

    #[test]
    fn rejects_non_http_schemes() {
        assert!(matches!(
            err("ftp://example.com/"),
            GuardError::UnsupportedScheme(_)
        ));
        assert!(matches!(
            err("file:///etc/passwd"),
            GuardError::UnsupportedScheme(_)
        ));
        assert!(matches!(
            err("gopher://example.com/"),
            GuardError::UnsupportedScheme(_)
        ));
        // data: URLs have no host and a non-http scheme.
        assert!(validate("data:text/plain,hello").is_err());
    }

    #[test]
    fn blocks_loopback_and_private_ipv4() {
        for raw in [
            "http://127.0.0.1/",
            "http://127.1.2.3/",
            "http://10.0.0.1/",
            "http://192.168.1.1/",
            "http://172.16.0.1/",
            "http://172.31.255.255/",
            "http://0.0.0.0/",
        ] {
            assert!(matches!(err(raw), GuardError::BlockedIp(_)), "{raw}");
        }
    }

    #[test]
    fn blocks_link_local_metadata_ip() {
        assert!(matches!(
            err("http://169.254.169.254/latest/meta-data/"),
            GuardError::BlockedIp(_)
        ));
    }

    #[test]
    fn blocks_cgnat_benchmarking_and_reserved() {
        assert!(matches!(
            err("http://100.64.0.1/"),
            GuardError::BlockedIp(_)
        ));
        assert!(matches!(
            err("http://198.18.0.1/"),
            GuardError::BlockedIp(_)
        ));
        assert!(matches!(err("http://240.0.0.1/"), GuardError::BlockedIp(_)));
        assert!(matches!(
            err("http://255.255.255.255/"),
            GuardError::BlockedIp(_)
        ));
    }

    #[test]
    fn blocks_alternate_ipv4_encodings() {
        // WHATWG URL parsing normalizes these numeric forms to 127.0.0.1, so a
        // string-only denylist would miss them but the IP check catches them.
        for raw in [
            "http://2130706433/",
            "http://0x7f.0.0.1/",
            "http://0177.0.0.1/",
        ] {
            assert!(matches!(err(raw), GuardError::BlockedIp(_)), "{raw}");
        }
    }

    #[test]
    fn blocks_loopback_and_ula_ipv6() {
        assert!(matches!(err("http://[::1]/"), GuardError::BlockedIp(_)));
        assert!(matches!(err("http://[::]/"), GuardError::BlockedIp(_)));
        assert!(matches!(err("http://[fe80::1]/"), GuardError::BlockedIp(_)));
        assert!(matches!(err("http://[fc00::1]/"), GuardError::BlockedIp(_)));
        assert!(matches!(
            err("http://[fd12:3456::1]/"),
            GuardError::BlockedIp(_)
        ));
    }

    #[test]
    fn blocks_ipv4_mapped_ipv6() {
        assert!(matches!(
            err("http://[::ffff:127.0.0.1]/"),
            GuardError::BlockedIp(_)
        ));
        assert!(matches!(
            err("http://[::ffff:169.254.169.254]/"),
            GuardError::BlockedIp(_)
        ));
    }

    #[test]
    fn blocks_transition_mechanism_embedded_private_ipv4() {
        // 6to4 wrapper for 127.0.0.1 (2002:7f00:0001::) and for 169.254.169.254.
        assert!(matches!(
            err("http://[2002:7f00:1::]/"),
            GuardError::BlockedIp(_)
        ));
        assert!(matches!(
            err("http://[2002:a9fe:a9fe::]/"),
            GuardError::BlockedIp(_)
        ));
        // NAT64 well-known prefix wrapping 127.0.0.1 and 10.0.0.1.
        assert!(matches!(
            err("http://[64:ff9b::7f00:1]/"),
            GuardError::BlockedIp(_)
        ));
        assert!(matches!(
            err("http://[64:ff9b::a00:1]/"),
            GuardError::BlockedIp(_)
        ));
    }

    #[test]
    fn allows_transition_mechanism_embedding_public_ipv4() {
        // 6to4 for 8.8.8.8 embeds a public address, which stays allowed.
        assert!(validate("http://[2002:808:808::]/").is_ok());
    }

    #[test]
    fn blocks_local_and_internal_hostnames() {
        for raw in [
            "http://localhost/",
            "http://LOCALHOST/",
            "http://foo.localhost/",
            "http://printer.local/",
            "http://db.internal/",
            "http://metadata.google.internal/",
            "http://service.home.arpa/",
        ] {
            assert!(matches!(err(raw), GuardError::BlockedHost(_)), "{raw}");
        }
    }

    #[test]
    fn documents_dns_rebinding_gap() {
        // `localtest.me` resolves to 127.0.0.1 in the real world, but the guard
        // cannot resolve names on Workers, so a name-based target that is not on
        // the denylist currently passes. This test pins that known behavior; see
        // the module docs for the mitigations that make it safe in practice.
        assert!(validate("http://localtest.me/").is_ok());
    }
}
