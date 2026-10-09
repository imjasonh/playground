//! Socket addresses that a traced command connects or sends to.

use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6};

const AF_UNIX: u16 = 1;
const AF_INET: u16 = 2;
const AF_INET6: u16 = 10;
const AF_NETLINK: u16 = 16;

#[derive(Clone, Debug, PartialEq, Eq)]
pub enum NetTarget {
    Inet(SocketAddr),
    /// A path-based Unix socket, as written by the program (maybe relative).
    Unix(Vec<u8>),
    Abstract(String),
    /// Netlink talks to the local kernel, for example to list interfaces.
    Netlink,
    /// `AF_UNSPEC` or an unnamed Unix socket: nothing outside the process.
    Unspecified,
    Other(u16),
}

/// Decodes a raw `struct sockaddr` of `len` bytes, as passed to `connect`,
/// `sendto`, or `sendmsg`.
pub fn parse_sockaddr(b: &[u8]) -> Option<NetTarget> {
    if b.len() < 2 {
        return None;
    }
    let family = u16::from_ne_bytes([b[0], b[1]]);
    Some(match family {
        0 => NetTarget::Unspecified,
        AF_INET if b.len() >= 8 => {
            let port = u16::from_be_bytes([b[2], b[3]]);
            let ip = Ipv4Addr::new(b[4], b[5], b[6], b[7]);
            NetTarget::Inet(SocketAddr::V4(SocketAddrV4::new(ip, port)))
        }
        AF_INET6 if b.len() >= 24 => {
            let port = u16::from_be_bytes([b[2], b[3]]);
            let mut ip = [0u8; 16];
            ip.copy_from_slice(&b[8..24]);
            let ip = Ipv6Addr::from(ip);
            NetTarget::Inet(SocketAddr::V6(SocketAddrV6::new(ip, port, 0, 0)))
        }
        AF_UNIX => {
            let path = &b[2..];
            if path.is_empty() {
                NetTarget::Unspecified
            } else if path[0] == 0 {
                let name = &path[1..];
                let name = name.split(|&c| c == 0).next().unwrap_or(name);
                NetTarget::Abstract(String::from_utf8_lossy(name).into_owned())
            } else {
                let end = path.iter().position(|&c| c == 0).unwrap_or(path.len());
                NetTarget::Unix(path[..end].to_vec())
            }
        }
        AF_NETLINK => NetTarget::Netlink,
        other => NetTarget::Other(other),
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    fn family(f: u16) -> [u8; 2] {
        f.to_ne_bytes()
    }

    #[test]
    fn inet() {
        let mut b = family(AF_INET).to_vec();
        b.extend_from_slice(&443u16.to_be_bytes());
        b.extend_from_slice(&[93, 184, 216, 34]);
        b.extend_from_slice(&[0; 8]);
        assert_eq!(
            parse_sockaddr(&b),
            Some(NetTarget::Inet("93.184.216.34:443".parse().unwrap()))
        );
    }

    #[test]
    fn inet6() {
        let mut b = family(AF_INET6).to_vec();
        b.extend_from_slice(&53u16.to_be_bytes());
        b.extend_from_slice(&[0; 4]);
        b.extend_from_slice(&Ipv6Addr::LOCALHOST.octets());
        b.extend_from_slice(&[0; 4]);
        assert_eq!(
            parse_sockaddr(&b),
            Some(NetTarget::Inet("[::1]:53".parse().unwrap()))
        );
    }

    #[test]
    fn unix() {
        let mut b = family(AF_UNIX).to_vec();
        b.extend_from_slice(b"/run/x.sock\0junk");
        assert_eq!(
            parse_sockaddr(&b),
            Some(NetTarget::Unix(b"/run/x.sock".to_vec()))
        );
        let mut b = family(AF_UNIX).to_vec();
        b.extend_from_slice(b"\0/tmp/.X11-unix/X0");
        assert_eq!(
            parse_sockaddr(&b),
            Some(NetTarget::Abstract("/tmp/.X11-unix/X0".into()))
        );
        assert_eq!(
            parse_sockaddr(&family(AF_UNIX)),
            Some(NetTarget::Unspecified)
        );
    }

    #[test]
    fn short_and_other() {
        assert_eq!(parse_sockaddr(&[1]), None);
        assert_eq!(
            parse_sockaddr(&family(AF_NETLINK)),
            Some(NetTarget::Netlink)
        );
        assert_eq!(parse_sockaddr(&family(17)), Some(NetTarget::Other(17)));
    }
}
