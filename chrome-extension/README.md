# Close Duplicate Tabs

A Chrome extension that closes extra tabs with the same URL. The toolbar button is the action. The badge on that button is the number of tabs the click will close. Chrome 150 and later also show that action on the tab menu.

The Chrome Web Store item ID is `canmakefmjmnhhaobdeipbamnalcloap`. This directory has no `index.html`, so GitHub Pages does not publish it.

Version `0.0.2` was a popup with no behavior, and the store rejected it because the listing did not describe a function. Version `0.1.0` is also rejected, so the store will not review that version again. Version `0.1.1` is the package to submit.

## What a click does

The service worker reads open tabs in every window. Tabs with the same URL are duplicates. The URL match is exact, including the query and the hash. `https://example.com/a` and `https://example.com/a/` are different. A tab with an empty URL is ignored. A tab that is still on `about:blank` is compared by its pending URL.

For each URL, the click keeps one tab and closes the others. It keeps a pinned tab ahead of an unpinned tab, then the active tab, then the tab you used most recently. If those are tied, it keeps the lower tab id.

The badge is that close count. It is empty when the count is 0. Counts above 999 render as `999+`. The button title is `Close N duplicate tabs`, or `No duplicate tabs` when the count is 0.

Right-click a tab in Chrome 150 or later and the menu shows the same title, `Close N duplicate tabs`. That item runs the same close as the toolbar button, so the number matches the badge. The item is hidden when the count is 0. Older Chrome keeps the toolbar button and does not show the item.

The extension uses the `tabs` permission so it can read URLs and close tabs. It uses `contextMenus` to add the tab menu item. It does not use host permissions or content scripts. URLs stay in the browser. The extension does not send them anywhere.

## Load it locally

1. Run `bash pack.sh` only if you want a zip. To load the directory unpacked, Chrome can point at this folder.
2. Open `chrome://extensions`, turn on Developer mode, and choose **Load unpacked**.
3. Open two tabs with the same URL. The badge shows `1`.
4. Click the toolbar button, or right-click a tab and choose **Close 1 duplicate tab**. One of those tabs closes, and the badge clears. Chrome older than 150 has the toolbar button only.

## Tests

From this directory:

```bash
npm test
```

`npm test` runs the Node tests. They cover which tabs close, the badge and tab menu, the store zip layout, the `tabs` and `contextMenus` permissions, and the listing image sizes.

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
| Summary | Closes extra tabs that share a URL. The badge and tab menu show how many tabs that click will close. |
| Single purpose | Add a toolbar button that closes extra tabs with the same URL, show how many tabs that click will close, and offer the same action from the tab menu. |
| Permission justification | The tabs permission lets the extension read each tab's URL, count tabs that share a URL, and close the extras. The contextMenus permission adds a Close N duplicate tabs item to the tab menu. N is the same count as the badge. The comparison happens on the device. The extension does not transmit tab URLs or titles. |
| Data use | It does not collect or use user data. |
| Visibility | Set this in the dashboard. The publish API cannot change it. |

Paste this as the detailed description:

```text
Close Duplicate Tabs adds one toolbar button. The badge on that button shows how many open tabs share a URL with another tab. That number is how many tabs the click will close.

Click the button to close those extra tabs. In Chrome 150 or later, right-click a tab and choose Close N duplicate tabs. That item closes the same tabs as the button, and it is hidden when there is nothing to close. For each URL, one tab stays open. A pinned tab stays ahead of an unpinned tab, then the active tab, then the tab you used most recently.

The extension reads tab URLs on your device to make that comparison. It does not send URLs, titles, or browsing history anywhere. It has no content scripts and does not change web pages.
```

The API cannot change Private or Public. If you change visibility, publish once in the dashboard. After this item is live, a push to `main` publishes a higher manifest version for you.

## Publish from main

`.github/workflows/chrome-extension.yml` runs the tests on pull requests and on pushes to `main`. It packs `chrome-extension.zip` and uploads that file as a workflow artifact. Download it from the run to inspect the package or to upload it in the developer dashboard.

On a push to `main` that changes this directory or the publish script, when the secrets below exist, the same job uploads that zip to item `canmakefmjmnhhaobdeipbamnalcloap` and calls the Chrome Web Store API v2 publish method.

The publish type defaults to `DEFAULT_PUBLISH`. After review, that version becomes the live version for the audience already saved on the item. Set the repository variable `CHROME_WEB_STORE_PUBLISH_TYPE` to `TRUSTED_TESTERS` or `STAGED_PUBLISH` to change that. A manual **Run workflow** on `main` publishes the current package too.

Increase `version` in `manifest.json` in the same change you want published. Each number is 0 through 65535, with at most four parts. The job skips a version that is already live or already in review. It fails, and does not upload, when the store has a newer version, when this version was rejected, or when a different version is still in review.

Add these repository secrets. The OAuth client needs the Chrome Web Store API enabled and the scope `https://www.googleapis.com/auth/chromewebstore`. The publisher ID is the account id in the developer dashboard URL. Google's guide is [Use the Chrome Web Store API](https://developer.chrome.com/docs/webstore/using-api).

| Secret | Value |
| --- | --- |
| `CHROME_WEB_STORE_CLIENT_ID` | OAuth client id |
| `CHROME_WEB_STORE_CLIENT_SECRET` | OAuth client secret |
| `CHROME_WEB_STORE_REFRESH_TOKEN` | Refresh token for the publisher account |
| `CHROME_WEB_STORE_PUBLISHER_ID` | Publisher id from the developer dashboard |

A refresh token for an OAuth app whose consent screen is in testing expires after 7 days. Use a production consent screen so the main-branch job can keep publishing.

Without those secrets, the workflow runs the tests and skips publish.
