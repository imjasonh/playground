# Playground no-op

A Chrome extension that shows one sentence and does nothing else. It declares no permissions, has no background script, and has no content scripts. Upload the zip as the first private item in the Chrome Web Store developer dashboard.

The package is Manifest V3, version `0.0.1`. It is not a GitHub Pages app, because this directory has no `index.html`.

## Build the zip

From this directory:

```bash
bash pack.sh /tmp/chrome-noop.zip
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

Use the same wording in the listing that the extension shows.

| Field | Value |
| --- | --- |
| Name | Playground no-op |
| Description | Shows one sentence and does nothing else. |
| Single purpose | This extension shows one sentence and does nothing else. |
| Data use | It does not collect or use user data. |
| Visibility | Private |

On the publisher **Account** page, the contact email has to be verified, and the Google account that will install the extension has to be listed under **Trusted tester accounts**. Submit this first version from the dashboard. Later API publishes keep the visibility saved there.
