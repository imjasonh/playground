//! Wi-Fi / DHCP refresh policy for a device that stays up indefinitely.
//!
//! lwIP's DHCP client is supposed to renew on its own, but a long-lived STA
//! can keep association while L3 dies (expired lease, stale DNS, NAT drop).
//! The firmware then sees `ESP_ERR_HTTP_CONNECT` with a still-valid-looking
//! LAN IP. Periodic DHCP renew plus reconnect-on-connect-failure recover
//! without a power cycle.

/// What the poll loop should do to the radio / DHCP client.
#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum WifiRefresh {
    None,
    /// Re-run DHCP while staying associated.
    RenewDhcp,
    /// Drop STA and associate again (same recovery as power-cycling the radio).
    Reconnect,
}

/// True when the HTTP client never got as far as a status line.
///
/// Heap / HTTP-status failures are *not* connect failures — those need a
/// different recovery (or none).
pub fn is_http_connect_failure(err: &str) -> bool {
    let upper = err.to_ascii_uppercase();
    if upper.contains("ESP_ERR_HTTP_CONNECT") || upper.contains("ESP_ERR_HTTP_CONNECTING") {
        return true;
    }
    if upper.contains("ESP_ERR_ESP_TLS") || upper.contains("ESP_ERR_MBEDTLS") {
        return true;
    }
    let dns = upper.contains("DNS");
    let dns_fail = upper.contains("FAIL") || upper.contains("ERR") || upper.contains("TIMEOUT");
    dns && dns_fail
}

/// Decide whether to renew DHCP or fully re-associate.
///
/// `refresh_secs == 0` disables the periodic renew (connect-failure and
/// dropped-STA recovery still run). Reconnects are gated by
/// `reconnect_cooldown_secs` so a dead AP does not tight-loop.
pub fn should_refresh_wifi(
    sta_connected: bool,
    netif_up: bool,
    connect_failure: bool,
    secs_since_refresh: u64,
    refresh_secs: u64,
    secs_since_reconnect: u64,
    reconnect_cooldown_secs: u64,
) -> WifiRefresh {
    let reconnect_ok = secs_since_reconnect >= reconnect_cooldown_secs;
    if !sta_connected {
        return if reconnect_ok {
            WifiRefresh::Reconnect
        } else {
            WifiRefresh::None
        };
    }
    if connect_failure && reconnect_ok {
        return WifiRefresh::Reconnect;
    }
    if !netif_up {
        return WifiRefresh::RenewDhcp;
    }
    if refresh_secs > 0 && secs_since_refresh >= refresh_secs {
        return WifiRefresh::RenewDhcp;
    }
    WifiRefresh::None
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn connect_error_is_detected() {
        assert!(is_http_connect_failure(
            "GET https://inkbot.example/ failed after 3 tries | http submit: ESP_ERR_HTTP_CONNECT"
        ));
        assert!(is_http_connect_failure("ESP_ERR_HTTP_CONNECTING"));
        assert!(is_http_connect_failure(
            "esp_tls: ESP_ERR_ESP_TLS_CANNOT_RESOLVE_HOSTNAME"
        ));
        assert!(is_http_connect_failure("DNS lookup failed"));
    }

    #[test]
    fn http_status_and_heap_are_not_connect_failures() {
        assert!(!is_http_connect_failure("GET / -> HTTP 502"));
        assert!(!is_http_connect_failure(
            "framebuffer must be 48000 bytes, got 12"
        ));
        assert!(!is_http_connect_failure("WIFI ERR step=connect"));
        assert!(!is_http_connect_failure(""));
    }

    #[test]
    fn dropped_sta_reconnects_after_cooldown() {
        assert_eq!(
            should_refresh_wifi(false, false, false, 10, 21600, 0, 120),
            WifiRefresh::None
        );
        assert_eq!(
            should_refresh_wifi(false, false, false, 10, 21600, 120, 120),
            WifiRefresh::Reconnect
        );
    }

    #[test]
    fn connect_failure_reconnects_when_sta_still_looks_up() {
        assert_eq!(
            should_refresh_wifi(true, true, true, 60, 21600, 120, 120),
            WifiRefresh::Reconnect
        );
        assert_eq!(
            should_refresh_wifi(true, true, true, 60, 21600, 30, 120),
            WifiRefresh::None
        );
    }

    #[test]
    fn periodic_dhcp_renew_when_healthy() {
        assert_eq!(
            should_refresh_wifi(true, true, false, 21599, 21600, 10_000, 120),
            WifiRefresh::None
        );
        assert_eq!(
            should_refresh_wifi(true, true, false, 21600, 21600, 10_000, 120),
            WifiRefresh::RenewDhcp
        );
    }

    #[test]
    fn netif_down_renews_dhcp_without_dropping_sta() {
        assert_eq!(
            should_refresh_wifi(true, false, false, 10, 21600, 10_000, 120),
            WifiRefresh::RenewDhcp
        );
    }

    #[test]
    fn zero_refresh_secs_disables_periodic_only() {
        assert_eq!(
            should_refresh_wifi(true, true, false, 100_000, 0, 10_000, 120),
            WifiRefresh::None
        );
        assert_eq!(
            should_refresh_wifi(true, true, true, 100_000, 0, 10_000, 120),
            WifiRefresh::Reconnect
        );
    }

    #[test]
    fn connect_failure_wins_over_periodic_renew() {
        assert_eq!(
            should_refresh_wifi(true, true, true, 21600, 21600, 120, 120),
            WifiRefresh::Reconnect
        );
    }
}
