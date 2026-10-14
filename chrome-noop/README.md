# Playground no-op

A private Chrome extension whose only feature is a toolbar popup. It requests no permissions, has no background script, and has no content scripts. The Chrome Web Store item ID is `canmakefmjmnhhaobdeipbamnalcloap`.

The package is Manifest V3, version `0.0.2`. This directory has no `index.html`, so GitHub Pages does not publish it.

## Build the zip

From this directory:

```bash
bash pack.sh chrome-noop.zip
```

`manifest.json` is at the root of the archive. The dashboard rejects a zip that wraps the files in an extra folder. Two listing images stay out of the zip:

- `store/icon-128.png` is the store icon. It is 128 by 128 pixels. The mark is 96 by 96, centered, with 16 pixels of transparent padding on each side.
- `store/screenshot.png` is the screenshot. It is 1280 by 800 pixels, 24-bit RGB, with no alpha channel.

To regenerate the icons and the screenshot, install Pillow and run `python3 render_assets.py`.

Check the package with:

```bash
bash pack_test.sh
```

## Dashboard fields

The store rejected version `0.0.1` because the listing description did not explain the functionality. Upload `chrome-noop.zip` on the draft, replace the listing text with the text below, and submit for review again. Leave visibility set to **Private**.

| Field | Value |
| --- | --- |
| Name | Playground no-op |
| Summary | Opens a toolbar popup. It requests no permissions and collects no data. |
| Single purpose | Add a toolbar button that opens a popup. The popup states that the extension requests no permissions and collects no data. |
| Data use | It does not collect or use user data. |
| Visibility | Private |

Paste this as the detailed description:

```text
Playground no-op adds one toolbar button. Click the button to open a popup. The popup states that the extension requests no permissions and collects no data.

The extension has no service worker and no content scripts. It does not read or change web pages. It does not access history, cookies, or tabs.

The publisher uses this private item to confirm that a trusted tester can install it from the Chrome Web Store.
```

On the publisher **Account** page, the contact email has to be verified, and the Google account that will install the extension has to be listed under **Trusted tester accounts**. Later API publishes keep the visibility saved there.
