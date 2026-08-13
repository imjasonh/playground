//! Path + method matching for the public and admin HTTP API.

#[derive(Debug, Clone, PartialEq, Eq)]
pub enum Route {
    Home,
    Post { id: i64 },
    Feed,
    Image { key: String },
    Subscribe,
    Admin,
    AdminLogin,
    AdminLogout,
    AdminPasskeys,
    AdminPasskeyRegisterOptions,
    AdminPasskeyRegisterVerify,
    AdminPasskeyDelete { id: i64 },
    AdminPosts,
    AdminPostDelete { id: i64 },
    AdminPostEdit { id: i64 },
    LoginPasskeyOptions,
    LoginPasskeyVerify,
}

/// Parse `method` (`GET`/`POST`) and a URL path (no query string) into a route.
pub fn parse(method: &str, path: &str) -> Option<Route> {
    let path = path.trim_end_matches('/');
    let path = if path.is_empty() { "/" } else { path };
    match (method, path) {
        ("GET", "/") => Some(Route::Home),
        ("GET", "/feed.xml") => Some(Route::Feed),
        ("GET", "/subscribe") | ("POST", "/subscribe") => Some(Route::Subscribe),
        ("GET", "/admin") => Some(Route::Admin),
        ("GET", "/admin/login") | ("POST", "/admin/login") => Some(Route::AdminLogin),
        ("POST", "/admin/logout") => Some(Route::AdminLogout),
        ("GET", "/admin/passkeys") => Some(Route::AdminPasskeys),
        ("POST", "/admin/passkeys/register/options") => Some(Route::AdminPasskeyRegisterOptions),
        ("POST", "/admin/passkeys/register/verify") => Some(Route::AdminPasskeyRegisterVerify),
        ("POST", "/admin/login/passkey/options") => Some(Route::LoginPasskeyOptions),
        ("POST", "/admin/login/passkey/verify") => Some(Route::LoginPasskeyVerify),
        ("POST", "/admin/posts") => Some(Route::AdminPosts),
        _ => {
            if method == "GET" {
                if let Some(id) = numeric_tail(path, "/post/") {
                    return Some(Route::Post { id });
                }
                if let Some(key) = path.strip_prefix("/img/") {
                    if !key.is_empty() {
                        return Some(Route::Image {
                            key: key.to_string(),
                        });
                    }
                }
            }
            if let Some(id) = id_before(path, "/admin/posts/", "/edit") {
                if method == "GET" || method == "POST" {
                    return Some(Route::AdminPostEdit { id });
                }
            }
            if method == "POST" {
                if let Some(id) = id_before(path, "/admin/posts/", "/delete") {
                    return Some(Route::AdminPostDelete { id });
                }
                if let Some(id) = id_before(path, "/admin/passkeys/", "/delete") {
                    return Some(Route::AdminPasskeyDelete { id });
                }
            }
            None
        }
    }
}

fn numeric_tail(path: &str, prefix: &str) -> Option<i64> {
    let rest = path.strip_prefix(prefix)?;
    parse_id(rest)
}

fn id_before(path: &str, prefix: &str, suffix: &str) -> Option<i64> {
    let rest = path.strip_prefix(prefix)?;
    let id = rest.strip_suffix(suffix)?;
    parse_id(id)
}

fn parse_id(s: &str) -> Option<i64> {
    crate::policy::parse_js_safe_id(s)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn public_routes() {
        assert_eq!(parse("GET", "/"), Some(Route::Home));
        assert_eq!(parse("GET", "/post/42"), Some(Route::Post { id: 42 }));
        assert_eq!(parse("GET", "/feed.xml"), Some(Route::Feed));
        assert_eq!(
            parse("GET", "/img/9/0.jpg"),
            Some(Route::Image {
                key: "9/0.jpg".into()
            })
        );
        assert_eq!(parse("GET", "/img/"), None);
        assert_eq!(parse("GET", "/post/abc"), None);
        assert_eq!(parse("GET", "/post/9007199254740992"), None);
        assert_eq!(parse("GET", "/subscribe"), Some(Route::Subscribe));
        assert_eq!(parse("POST", "/subscribe"), Some(Route::Subscribe));
        assert_eq!(parse("GET", "/subscribe/"), Some(Route::Subscribe));
        assert_eq!(
            parse("GET", "/img/assets/paperclip.png"),
            Some(Route::Image {
                key: "assets/paperclip.png".into()
            })
        );
    }

    #[test]
    fn admin_routes() {
        assert_eq!(parse("GET", "/admin"), Some(Route::Admin));
        assert_eq!(parse("POST", "/admin/posts"), Some(Route::AdminPosts));
        assert_eq!(
            parse("POST", "/admin/posts/7/delete"),
            Some(Route::AdminPostDelete { id: 7 })
        );
        assert_eq!(
            parse("GET", "/admin/posts/7/edit"),
            Some(Route::AdminPostEdit { id: 7 })
        );
        assert_eq!(
            parse("POST", "/admin/posts/7/edit"),
            Some(Route::AdminPostEdit { id: 7 })
        );
        assert_eq!(
            parse("POST", "/admin/passkeys/3/delete"),
            Some(Route::AdminPasskeyDelete { id: 3 })
        );
        assert_eq!(parse("GET", "/admin/posts/7/delete"), None);
        assert_eq!(parse("GET", "/admin/login"), Some(Route::AdminLogin));
        assert_eq!(parse("POST", "/admin/login"), Some(Route::AdminLogin));
        assert_eq!(parse("POST", "/admin/logout"), Some(Route::AdminLogout));
        assert_eq!(parse("GET", "/admin/passkeys"), Some(Route::AdminPasskeys));
        assert_eq!(
            parse("POST", "/admin/passkeys/register/options"),
            Some(Route::AdminPasskeyRegisterOptions)
        );
        assert_eq!(
            parse("POST", "/admin/passkeys/register/verify"),
            Some(Route::AdminPasskeyRegisterVerify)
        );
        assert_eq!(
            parse("POST", "/admin/login/passkey/options"),
            Some(Route::LoginPasskeyOptions)
        );
        assert_eq!(
            parse("POST", "/admin/login/passkey/verify"),
            Some(Route::LoginPasskeyVerify)
        );
        assert_eq!(parse("GET", "/admin/"), Some(Route::Admin));
        assert_eq!(parse("POST", "/admin"), None);
        assert_eq!(parse("GET", "/nope"), None);
    }
}
