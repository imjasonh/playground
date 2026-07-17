# Inside Bubble Man Stage

An interactive, playable explanation of how the Bubble Man Stage theme from
*Mega Man 2* is represented in the NES ROM.

The app reconstructs selected passages with the Web Audio API, displays their
four channel streams as a piano roll, and follows the corresponding
reverse-engineered music bytecode.

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
