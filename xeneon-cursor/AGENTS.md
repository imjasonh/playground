# Agent guide: xeneon-cursor

Touch-first Cursor cloud-agent HUD for the Corsair XENEON EDGE (14.5″ / 2560×720).
See `README.md` for install, run, and test instructions.

## Visual direction

Match **Cursor Dark** (flat near-black chrome/content, soft borders, blue
primary `#81A1C1`, system UI fonts). Avoid neon gradients, glow pulses, oversized
display type, and generic “AI dashboard” chrome.

## Input

No on-screen keyboard. Fields are normal focused inputs: tap to focus, then type
or paste with the Mac keyboard. Opening New agent / Follow-up focuses the prompt.

## Pull request screenshots

When you open or update a pull request that changes this app’s UI (or behavior
visible in the HUD), take **representative screenshots** of the areas affected
by the change and **post them as PR comments**.

- Capture the views that actually changed (or the flows a reviewer needs to see).
- Use **realistic proportions** for the XENEON strip: prefer ~2560×720 (or the
  same ~32:9 aspect) rather than a tall phone/desktop crop.
- Prefer mock mode (`npm run dev`) when a live API key is unavailable.
- Attach images in a PR comment (or update an existing screenshot comment) so
  reviewers can judge the change without running the app locally.
