# Sundial

A clock that casts a long shadow the same way a sundial does. During the
day only the shadow is visible. After sunset the shadow is gone and the
numerals show.

The screen is a horizontal plate with north at the top. Sun position comes
from the time on your clock. Your latitude and longitude default to your
time zone's location (`America/New_York` sits at New York, not the middle
of the Eastern meridian), so sunrise and sunset land near where you are
without asking for anything. **Use location** refines that to your exact
coordinates. After you grant it, the button goes away and the page keeps
using that fix. The page does not ask until you click it. If you want a
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
