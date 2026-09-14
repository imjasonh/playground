# Inside Bubble Man Stage

An interactive, playable explanation of how the Bubble Man Stage theme from
*Mega Man 2* is represented in the NES ROM.

The app reconstructs the complete 32-bar first pass from the four
reverse-engineered channel streams. It plays each eight-bar narrative section in
full and offers a complete-song mode whose 24-bar body loops at the same point
encoded in the ROM. Playback uses the Web Audio API and follows the corresponding
bytecode in a piano-roll view.

## Run locally

```bash
npm start
```

Then open <http://localhost:3000>.

## Test

```bash
npm test
npm run test:e2e
```

End-to-end tests use Playwright Chromium and mobile WebKit. They assert that the
audio graph produces a non-zero signal and cover synchronized bytecode
highlighting, channel muting, passage navigation, and mobile overflow.

The playback is an educational browser reconstruction, not an emulator. Note
sequences and addresses follow the commented sound-driver disassembly; browser
envelopes and mixing are approximations.
