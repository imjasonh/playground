//! Delayed post-notification email: bodies, tokens, and the 1-minute window.
//!
//! The Worker schedules `notify_at = created_at + NOTIFY_DELAY_SECS` on publish
//! and a cron later sends only if the post still exists and has not been
//! marked notified. Transport (D1 / `send_email`) stays in `worker_entry`.

use rand_core::{OsRng, RngCore};

/// Wait this long after publish so the author can delete a post and skip mail.
pub const NOTIFY_DELAY_SECS: i64 = 60;

const SUBJECT_MAX_CHARS: usize = 72;
const TOKEN_BYTES: usize = 16;

/// Unix time when a post created at `created_at` should be emailed.
pub fn notify_at(created_at: i64) -> i64 {
    created_at.saturating_add(NOTIFY_DELAY_SECS)
}

/// True when this post is past its delay, not yet mailed, and still due.
pub fn is_due(now: i64, notify_at: i64, notified_at: Option<i64>) -> bool {
    notified_at.is_none() && notify_at <= now
}

/// Interest-list rows are mailed; unsubscribed addresses are not.
pub fn should_receive(status: &str) -> bool {
    status != "unsubscribed"
}

/// Strip CR/LF so a post body cannot inject email headers.
pub fn sanitize_header(s: &str) -> String {
    s.chars().filter(|c| *c != '\r' && *c != '\n').collect()
}

/// 32-char hex token for unsubscribe links.
pub fn new_subscriber_token() -> String {
    let mut bytes = [0u8; TOKEN_BYTES];
    OsRng.fill_bytes(&mut bytes);
    hex::encode(bytes)
}

pub fn permalink(site_url: &str, post_id: i64) -> String {
    format!("{}/post/{post_id}", site_url.trim_end_matches('/'))
}

pub fn unsubscribe_url(site_url: &str, token: &str) -> String {
    format!(
        "{}/unsubscribe?token={token}",
        site_url.trim_end_matches('/')
    )
}

pub fn post_subject(site_title: &str, body: &str) -> String {
    let title = sanitize_header(site_title.trim());
    let body = sanitize_header(body.trim());
    if body.is_empty() {
        return format!("new post on {title}");
    }
    let mut chars = body.chars();
    let mut out = String::new();
    for _ in 0..SUBJECT_MAX_CHARS.saturating_sub(1) {
        match chars.next() {
            Some(c) => out.push(c),
            None => return out,
        }
    }
    match (chars.next(), chars.next()) {
        (None, _) => out,
        (Some(_), None) => body,
        (Some(_), Some(_)) => {
            out.push('…');
            out
        }
    }
}

pub fn post_text(site_url: &str, post_id: i64, body: &str, unsub_url: &str) -> String {
    let link = permalink(site_url, post_id);
    let body = body.trim();
    if body.is_empty() {
        format!("{link}\n\n---\nUnsubscribe: {unsub_url}\n")
    } else {
        format!("{body}\n\n{link}\n\n---\nUnsubscribe: {unsub_url}\n")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn delay_is_one_minute() {
        assert_eq!(NOTIFY_DELAY_SECS, 60);
        assert_eq!(notify_at(1_000), 1_060);
        assert_eq!(notify_at(i64::MAX), i64::MAX);
    }

    #[test]
    fn due_only_after_delay_and_until_sent() {
        assert!(!is_due(1_059, 1_060, None));
        assert!(is_due(1_060, 1_060, None));
        assert!(is_due(1_120, 1_060, None));
        assert!(!is_due(1_120, 1_060, Some(1_061)));
    }

    #[test]
    fn pending_and_confirmed_receive_unsubscribed_does_not() {
        assert!(should_receive("pending"));
        assert!(should_receive("confirmed"));
        assert!(!should_receive("unsubscribed"));
    }

    #[test]
    fn headers_drop_crlf() {
        assert_eq!(sanitize_header("a\r\nb\nc"), "abc");
    }

    #[test]
    fn subject_clips_and_falls_back() {
        assert_eq!(post_subject("y", ""), "new post on y");
        assert_eq!(post_subject("y", "  hi\nthere  "), "hithere");
        assert_eq!(post_subject("y", "short"), "short");
        let long = "a".repeat(80);
        let sub = post_subject("y", &long);
        assert!(sub.ends_with('…'));
        assert_eq!(sub.chars().count(), SUBJECT_MAX_CHARS);
        assert!(!sub.contains('\n'));
    }

    #[test]
    fn text_includes_permalink_and_unsub() {
        let t = post_text(
            "https://y.example",
            9,
            "hello",
            "https://y.example/unsubscribe?token=abc",
        );
        assert!(t.contains("hello"));
        assert!(t.contains("https://y.example/post/9"));
        assert!(t.contains("token=abc"));
        let img = post_text("https://y.example/", 3, "  ", "https://u");
        assert!(!img.starts_with('\n'));
        assert!(img.contains("/post/3"));
        assert!(img.contains("https://u"));
    }

    #[test]
    fn urls_trim_trailing_slash() {
        assert_eq!(
            permalink("https://y.example/", 1),
            "https://y.example/post/1"
        );
        assert_eq!(
            unsubscribe_url("https://y.example/", "ab"),
            "https://y.example/unsubscribe?token=ab"
        );
    }

    #[test]
    fn token_is_32_hex_chars() {
        let a = new_subscriber_token();
        let b = new_subscriber_token();
        assert_eq!(a.len(), 32);
        assert_eq!(b.len(), 32);
        assert_ne!(a, b);
        assert!(a.chars().all(|c| c.is_ascii_hexdigit()));
    }
}
