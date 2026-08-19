# Before and after

Rewrite toward the recommended column. Don't apply these as mechanical find-and-replace when the surrounding sentence would become worse.

## Documentation

| Not recommended | Recommended |
| --- | --- |
| Click on the button below to simply save your changes! | To save your changes, click **Save**. |
| See [the guide](https://example.com) for more information. | For more information about authentication, see [Passkeys](https://example.com). |
| This page will show you how we currently handle previews. | This document explains how preview deploys work. |
| The server should return a 200. | The server returns `200` if the token is valid. |
| You can also utilize the CLI via SSH. | You can also run the command over SSH. |
| Once the build finishes, the app will be deployed. | After the build finishes, the workflow deploys the app. |
| Don't use the legacy master/slave flags. | Don't use the deprecated primary and replica flags (`--master`, `--slave`). |

## API comments

```go
// Not recommended:
// This function parses the path. It will return an error if
// the path is empty. You should call this before Open.

// Recommended:
// Parse parses a repository path.
// If path is empty, Parse returns ErrEmptyPath.
// Call Parse before Open.
func Parse(path string) (Repo, error)
```

```rust
// Not recommended:
/// This helper just checks the allow list and
/// tells the caller whether they can proceed.

// Recommended:
/// Returns whether `principal` is on the allowlist.
///
/// An empty allowlist permits every principal. This matches
/// the Worker default so local tests don't need fixture data.
fn allowed(principal: &str) -> bool
```

## Inline comments

```javascript
// Not recommended:
// Increment i by 1
i += 1;

// Recommended:
// Skip the header row. The CSV writer already added column names.
i += 1;
```

```go
// Not recommended:
// We check if err is nil here so we don't crash.

// Recommended:
// A nil err still means the body may be empty; treat that
// as success so callers can distinguish I/O failures.
if err != nil {
    return err
}
```
