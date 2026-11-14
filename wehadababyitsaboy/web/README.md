# whbiab.js

A tracking pixel for the browser apps. On each page load, `whbiab.js` requests
an image that doesn't exist from the [`wehadababyitsaboy`](..) bucket. The
bucket answers `403`, and its usage log keeps the request.

## Add it to an app

```bash
bash .github/scripts/check-whbiab-web.sh --fix
```

The command links `whbiab.js` into every browser app that lacks it and adds
this tag before `</body>` in each `index.html`:

```html
<script src="whbiab.js" data-app="my-app"></script>
```

`data-app` is the app's directory name. If the page sets a
`Content-Security-Policy`, add `https://storage.googleapis.com` to `img-src`;
the command reports a page that doesn't.

There is one `whbiab.js`, this one. Each app's `whbiab.js` is a symbolic link
to it (`../wehadababyitsaboy/web/whbiab.js`), so an edit here reaches every app.
A link is needed because each app deploys from its own directory, and a page
that loaded the file from outside that directory would get a 404 when served
locally, which fails a test that watches the console. The deploy and preview
workflows copy each app with `cp -rL`, so the published app holds the file
itself. Without `--fix`, the command only checks, and the Test job runs that
check.

## Posts

`build-blog.py` copies this file into `/posts/whbiab.js`, and the
templates in `.github/pages/` load it. The index loads
`whbiab.js` with `data-app="posts"`. Each post, one directory down, loads
`../whbiab.js` with `data-app="posts-<directory>"`. `<directory>` is the
post's parent directory, which is also the URL slug. The feed does not
load the script.

## What a ping contains

```
https://storage.googleapis.com/wehadababyitsaboy/my-app/web.touch.dark.phone?bob=wehadababyitsaboy&lang=en
```

- The path starts with the app name, then `web` and the context, joined with
  dots: `touch` or `mouse` for the primary pointer, `dark` or `light` for the
  color scheme, `standalone` for an installed app, and `phone` (under 600 px),
  `tablet` (under 1024 px), or `desktop` for the window width.
- `lang` is the browser's primary language, such as `en`.

The usage log also records the visitor's IP address and `User-Agent`. The
request sends no referrer. The page's URL, title, and contents never leave the
page.

## When nothing is sent

The script sends nothing from `localhost` or a file, so local development and
the Playwright tests don't count. It also sends nothing from any host other
than `imjasonh.github.io`, from a browser that sets Do Not Track or Global
Privacy Control, or from a browser under automation. A PR preview on that host
is counted. Its query adds `preview=pr-<N>`, for example `preview=pr-732`.

## Test

```bash
bash .github/scripts/check-whbiab-web_test.sh
```

That runs `whbiab.test.js` with the Node test runner and checks every browser
app.
