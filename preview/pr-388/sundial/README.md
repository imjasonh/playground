# Sundial

A clock that casts a long shadow the same way a sundial does. During the
day only the shadow is visible. After sunset the shadow is gone and the
numerals show.

The screen is a horizontal plate with north at the top. Sun position comes
from the time on your clock. Longitude is inferred from the time zone;
latitude defaults to 40.7°N. **Use location** asks for your coordinates.
After you grant it, the button goes away and the page keeps using that
fix. The page does not ask until you click it. If you want a
specific place without sharing a location, pass `lat` and `lon` in the
query string. To pin the clock to a moment, add an `at` parameter with an
ISO timestamp.

Drag, or use the arrow keys, to move through the day. Press Escape to
return to now.

## Run locally

```bash
npm start
```

Open http://localhost:3000. Tests:

```bash
npm test
```
