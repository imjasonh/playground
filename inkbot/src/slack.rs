//! Slack Events API parsing for `@inkbot` image mentions.

use serde::Deserialize;
use serde_json::Value;

/// Outcome of parsing a Slack Events API POST body.
#[derive(Debug, PartialEq, Eq)]
pub enum SlackEvent {
    /// URL verification handshake during app install.
    UrlVerification { challenge: String },
    /// `@inkbot` mention that may carry image attachments.
    AppMention(AppMention),
    /// Anything else we ignore (message_changed, retries we don't handle, …).
    Ignored,
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct AppMention {
    pub channel: String,
    pub user: String,
    pub text: String,
    pub ts: String,
    pub thread_ts: Option<String>,
    pub files: Vec<SlackFile>,
    event_id: Option<String>,
}

impl AppMention {
    pub fn event_id(&self) -> Option<&str> {
        self.event_id.as_deref()
    }

    /// Prefer an explicit thread; otherwise reply under the mention itself.
    pub fn reply_thread_ts(&self) -> &str {
        self.thread_ts.as_deref().unwrap_or(&self.ts)
    }

    /// First image-ish file, if any.
    pub fn first_image(&self) -> Option<&SlackFile> {
        self.files.iter().find(|f| f.is_image())
    }
}

#[derive(Debug, Clone, PartialEq, Eq)]
pub struct SlackFile {
    pub id: String,
    pub name: String,
    pub mimetype: String,
    /// Private download URL; requires `Authorization: Bearer <bot token>`.
    pub url_private_download: String,
}

impl SlackFile {
    pub fn is_image(&self) -> bool {
        if self.mimetype.starts_with("image/") {
            return true;
        }
        // Slack sometimes labels uploads as octet-stream; trust the filename.
        self.mimetype == "application/octet-stream" && looks_like_image_name(&self.name)
    }
}

fn looks_like_image_name(name: &str) -> bool {
    let lower = name.to_ascii_lowercase();
    lower.ends_with(".png")
        || lower.ends_with(".jpg")
        || lower.ends_with(".jpeg")
        || lower.ends_with(".gif")
        || lower.ends_with(".webp")
}

#[derive(Debug, Deserialize)]
struct Envelope {
    #[serde(rename = "type")]
    kind: Option<String>,
    challenge: Option<String>,
    event_id: Option<String>,
    event: Option<EventBody>,
}

#[derive(Debug, Clone, Deserialize)]
struct EventBody {
    #[serde(rename = "type")]
    kind: Option<String>,
    channel: Option<String>,
    user: Option<String>,
    text: Option<String>,
    ts: Option<String>,
    thread_ts: Option<String>,
    files: Option<Vec<FileBody>>,
    /// Sometimes files live on a nested message (e.g. thread broadcasts).
    message: Option<Box<EventBody>>,
}

#[derive(Debug, Clone, Deserialize)]
struct FileBody {
    id: Option<String>,
    name: Option<String>,
    mimetype: Option<String>,
    url_private_download: Option<String>,
    url_private: Option<String>,
}

/// Parse a Slack Events API JSON body into a typed event.
pub fn parse_event(body: &[u8]) -> Result<SlackEvent, String> {
    let env: Envelope =
        serde_json::from_slice(body).map_err(|e| format!("invalid slack json: {e}"))?;

    if env.kind.as_deref() == Some("url_verification") {
        let challenge = env
            .challenge
            .filter(|c| !c.is_empty())
            .ok_or_else(|| "missing challenge".to_string())?;
        return Ok(SlackEvent::UrlVerification { challenge });
    }

    let Some(event) = env.event else {
        return Ok(SlackEvent::Ignored);
    };

    if event.kind.as_deref() != Some("app_mention") {
        return Ok(SlackEvent::Ignored);
    }

    // Prefer files on the event; fall back to nested message.files.
    let files_src = event
        .files
        .clone()
        .or_else(|| event.message.as_ref().and_then(|m| m.files.clone()))
        .unwrap_or_default();

    let channel = event
        .channel
        .filter(|c| !c.is_empty())
        .ok_or_else(|| "app_mention missing channel".to_string())?;
    let user = event.user.unwrap_or_default();
    let text = event.text.unwrap_or_default();
    let ts = event
        .ts
        .filter(|t| !t.is_empty())
        .ok_or_else(|| "app_mention missing ts".to_string())?;

    let files = files_src
        .into_iter()
        .filter_map(|f| {
            let url = f
                .url_private_download
                .or(f.url_private)
                .filter(|u| !u.is_empty())?;
            Some(SlackFile {
                id: f.id.unwrap_or_default(),
                name: f.name.unwrap_or_else(|| "image".into()),
                mimetype: f
                    .mimetype
                    .unwrap_or_else(|| "application/octet-stream".into()),
                url_private_download: url,
            })
        })
        .collect();

    Ok(SlackEvent::AppMention(AppMention {
        channel,
        user,
        text,
        ts,
        thread_ts: event.thread_ts,
        files,
        event_id: env.event_id,
    }))
}

/// Build the JSON body for `chat.postMessage`.
pub fn reply_payload(channel: &str, thread_ts: &str, text: &str) -> Value {
    serde_json::json!({
        "channel": channel,
        "thread_ts": thread_ts,
        "text": text,
    })
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn url_verification() {
        let body = br#"{"type":"url_verification","challenge":"abc123"}"#;
        match parse_event(body).unwrap() {
            SlackEvent::UrlVerification { challenge } => assert_eq!(challenge, "abc123"),
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn app_mention_with_image() {
        let body = br#"{
            "token":"x","team_id":"T","api_app_id":"A",
            "event":{
                "type":"app_mention",
                "user":"U1",
                "text":"<@Ubot> show this",
                "ts":"1710000000.000100",
                "channel":"C1",
                "files":[{
                    "id":"F1",
                    "name":"cat.jpg",
                    "mimetype":"image/jpeg",
                    "url_private_download":"https://files.slack.com/files-pri/T-F/download/cat.jpg"
                }]
            },
            "type":"event_callback",
            "event_id":"Ev1"
        }"#;
        match parse_event(body).unwrap() {
            SlackEvent::AppMention(m) => {
                assert_eq!(m.channel, "C1");
                assert_eq!(m.reply_thread_ts(), "1710000000.000100");
                assert_eq!(m.first_image().unwrap().name, "cat.jpg");
                assert_eq!(m.event_id(), Some("Ev1"));
            }
            other => panic!("unexpected {other:?}"),
        }
    }

    #[test]
    fn ignore_other_events() {
        let body = br#"{"type":"event_callback","event":{"type":"message","text":"hi"}}"#;
        assert_eq!(parse_event(body).unwrap(), SlackEvent::Ignored);
    }
}
