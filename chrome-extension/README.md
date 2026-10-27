# Close Duplicate Tabs

A Chrome extension that closes extra tabs with the same URL, and copies decoded base64 from the selection menu. The toolbar button closes the extra tabs. The badge on that button is the number of tabs the click will close. Chrome 150 and later also show that action on the tab menu.

The Chrome Web Store item ID is `cfmebakopkdpedmdbpcpfibhodmppigj`. That item is already published to trusted testers. This directory has no `index.html`, so GitHub Pages does not publish it.

Version `0.0.2` was a popup with no behavior, and the store rejected it because the listing did not describe a function. Version `0.1.0` is also rejected, so the store will not review that version again. Version `0.1.1` is in review. Version `0.1.3` is the package to submit.

## What a click does

The service worker reads open tabs in every window. Tabs with the same URL are duplicates. The URL match is exact, including the query and the hash. `https://example.com/a` and `https://example.com/a/` are different. A tab with an empty URL is ignored. A tab that is still on `about:blank` is compared by its pending URL.

For each URL, the click keeps one tab and closes the others. It keeps a pinned tab ahead of an unpinned tab, then the active tab, then the tab you used most recently. If those are tied, it keeps the lower tab id.

The badge is that close count. It is empty when the count is 0. Counts above 999 render as `999+`. The button title is `Close N duplicate tabs`, or `No duplicate tabs` when the count is 0.

Right-click a tab in Chrome 150 or later and the menu shows the same title, `Close N duplicate tabs`. That item runs the same close as the toolbar button, so the number matches the badge. The item is hidden when the count is 0. Older Chrome keeps the toolbar button and does not show the item.

## What a selection does

Highlight text on an `http` or `https` page and right-click. The extension trims whitespace from the ends of the selection. If the remaining text is not standard base64, the menu does not add an item. Standard base64 uses the alphabet A-Z, a-z, 0-9, `+`, and `/`, with `=` padding, and its length is a multiple of 4. Whitespace in the middle of the selection stays, so a string with a space in the middle is not base64.

If the selection is standard base64 and the decoded bytes are UTF-8 text that is not only whitespace, the menu shows that text. A short string can still be valid base64. Highlighting `file` shows `~)^`. Click the item to copy the decoded text. Line breaks in the decoded text stay in the copy. The menu title is one line, so those breaks appear as spaces there. A `%s` in the decoded text is shown with a zero-width space so Chrome does not replace it with the selection.

The content script reads the highlighted text, including text in a text field, and sends it to the service worker. It does not change the page. The service worker decodes it and updates the menu before the click. The click copies through an offscreen document. The selection and the decoded text stay on the device.

The extension uses the `tabs` permission so it can read URLs and close tabs. It uses `contextMenus` for the tab item and the selection item. The content script matches `http://*/*` and `https://*/*`. The manifest has no `host_permissions` entry. It uses `clipboardWrite` and `offscreen` to copy the decoded text. The extension does not send tab URLs, titles, or selected text anywhere.

## Load it locally

1. Run `bash pack.sh` only if you want a zip. To load the directory unpacked, Chrome can point at this folder.
2. Open `chrome://extensions`, turn on Developer mode, and choose **Load unpacked**.
3. Open two tabs with the same URL. The badge shows `1`.
4. Click the toolbar button, or right-click a tab and choose **Close 1 duplicate tab**. One of those tabs closes, and the badge clears. Chrome older than 150 has the toolbar button only.
5. On an https page, select `aGVsbG8=`, right-click, and choose `hello`. That copies `hello`.

## Tests

From this directory:

```bash
npm test
```

`npm test` runs the Node tests. They cover which tabs close, the badge and tab menu, base64 detection, the selection menu, the clipboard write, the store zip layout, the permissions, and the listing image sizes.

`node chrome_smoke.js` loads this directory in headless Chrome, opens two tabs with the same URL, and checks that the badge matches the close count. It checks that the tab menu item is registered, then runs the toolbar action and checks that the badge clears. Chrome 154 or newer is required, because the script uses the DevTools `Extensions.loadUnpacked` and `Extensions.triggerAction` commands.

Regenerate the icons with Pillow:

```bash
python3 render_assets.py
```

Replace the store screenshots by running Chrome and capturing the window:

```bash
CHROME_BIN=/path/to/chrome-for-testing python3 capture_screenshot.py
```

`capture_screenshot.py` needs Xvfb, ImageMagick's `import`, and `xdotool`. Branded Chrome ignores `--load-extension`, so the binary has to be Chrome for Testing. `store/screenshot.png` is that window with four tabs at the same URL. The toolbar badge is 3, which is how many of those tabs the click would close. `store/screenshot-closed.png` is the same window after the click.

## Store listing

Upload `chrome-extension.zip` from `bash pack.sh chrome-extension.zip` if you are submitting the draft by hand. Replace the listing text with the text below. The screenshot and the store icon stay out of the zip.

| File | Use |
| --- | --- |
| `store/icon-128.png` | Store icon, 128 by 128. The mark is 96 by 96, centered, with 16 pixels of padding. |
| `store/screenshot.png` | Listing screenshot, 1280 by 800, 24-bit RGB. A capture of Chrome with four tabs at the same URL and a toolbar badge of 3. |
| `store/screenshot-closed.png` | The same window after the toolbar click. |

| Field | Value |
| --- | --- |
| Name | Close Duplicate Tabs |
| Summary | Closes extra tabs that share a URL. The badge shows that count. Selected base64 adds a menu item that copies the decoded text. |
| Single purpose | Add a toolbar button that closes extra tabs with the same URL, show how many tabs that click will close, offer the same action from the tab menu, and copy decoded base64 from the selection menu. |
| Permission justification | The tabs permission lets the extension read each tab's URL, count tabs that share a URL, and close the extras. The contextMenus permission adds a Close N duplicate tabs item to the tab menu and a selection item when the highlighted text is base64. N is the same count as the badge. The content script reads the highlighted text on http and https pages so that item can show the decoded text. It does not modify pages. The clipboardWrite and offscreen permissions copy the decoded text to the clipboard when that item is clicked. Decoding and the URL comparison happen on the device. The extension does not transmit tab URLs, titles, or selected text. |
| Data use | It does not collect or transmit user data. It reads tab URLs and highlighted text on the device to close duplicate tabs and to copy decoded base64. |
| Visibility | Set this in the dashboard. The publish API cannot change it. |

Paste this as the detailed description:

```text
Close Duplicate Tabs adds one toolbar button. The badge on that button shows how many open tabs share a URL with another tab. That number is how many tabs the click will close.

Click the button to close those extra tabs. In Chrome 150 or later, right-click a tab and choose Close N duplicate tabs. That item closes the same tabs as the button, and it is hidden when there is nothing to close. For each URL, one tab stays open. A pinned tab stays ahead of an unpinned tab, then the active tab, then the tab you used most recently.

Highlight base64 text on a web page and right-click. If the selection is standard base64, the menu shows the decoded text. Click that item to copy the decoded text. If the selection is not base64, the menu does not add an item.

The extension reads tab URLs and the highlighted text on your device. It does not send URLs, titles, selected text, or the decoded text anywhere. The content script does not change web pages.
```

The API cannot change Private or Public. If you change visibility, publish once in the dashboard. After this item is live, a push to `main` publishes a higher manifest version for you.

## Publish from main

`.github/workflows/chrome-extension.yml` runs the tests on pull requests and on pushes to `main`. It packs `chrome-extension.zip` and uploads that file as a workflow artifact. Download it from the run to inspect the package or to upload it in the developer dashboard.

On a push to `main` that changes this directory or the publish script, a separate `publish` job downloads that zip, mints a Chrome Web Store access token over GitHub OIDC, and calls the Chrome Web Store API v2 publish method on item `cfmebakopkdpedmdbpcpfibhodmppigj`.

The publish type defaults to `DEFAULT_PUBLISH`. The job first asks the store to publish without review. When the store requires review, the job submits the same draft for review. After review, that version becomes the live version for the audience already saved on the item, which is trusted testers. Set the repository variable `CHROME_WEB_STORE_PUBLISH_TYPE` to `STAGED_PUBLISH` to hold the approved package until you publish it. The API v2 publish type has no trusted-tester value. A manual **Run workflow** on `main` publishes the current package too.

Increase `version` in `manifest.json` in the same change you want published. Each number is 0 through 65535, with at most four parts. The job skips a version that is already live or already in review. It fails, and does not upload, when the store has a newer version, when this version was rejected, or when a different version is still in review.

### Authentication

Publishing does not store a Chrome Web Store OAuth client secret or refresh token in GitHub. It reuses the GitHub Actions Workload Identity Federation pool [`gcp/terraform`](../gcp/README.md) creates for Cloud Run deploys. That stack also creates a third Workload Identity provider and a Google Cloud service account bound only to it, with no GCP project roles: `google-github-actions/auth` impersonates that account over OIDC and asks IAM to mint it a short-lived access token scoped to `https://www.googleapis.com/auth/chromewebstore`, which `.github/scripts/chrome_web_store.py` uses directly.

The Chrome Web Store only honors that token after the service account's email is linked on the publisher in the developer dashboard (**Account > API access**; a publisher can link one service account) — that link is a one-time manual step `gcp/terraform` cannot do. See [`gcp/README.md`](../gcp/README.md) for applying that stack and setting up the `chrome-webstore` GitHub environment.

Add the repository secret below, and the two environment variables `tofu output chrome_webstore_github_actions_variables` prints to the `chrome-webstore` GitHub environment.

| Name | Where | Value |
| --- | --- | --- |
| `CHROME_WEBSTORE_WORKLOAD_IDENTITY_PROVIDER` | `chrome-webstore` environment variable | `tofu output chrome_webstore_workload_identity_provider` |
| `CHROME_WEBSTORE_SERVICE_ACCOUNT` | `chrome-webstore` environment variable | `tofu output chrome_webstore_service_account` |
| `CHROME_WEB_STORE_PUBLISHER_ID` | Repository secret | Publisher id from the developer dashboard |

Without those, the workflow runs the tests and skips publish.

`.github/scripts/chrome_web_store.py` also still accepts the older OAuth refresh-token flow (`CHROME_WEB_STORE_CLIENT_ID`, `CHROME_WEB_STORE_CLIENT_SECRET`, `CHROME_WEB_STORE_REFRESH_TOKEN`) when `CHROME_WEB_STORE_ACCESS_TOKEN` isn't set, which is useful for a one-off publish from a laptop. A refresh token for an OAuth app whose consent screen is in testing expires after 7 days, which is why the main-branch job no longer uses one.
