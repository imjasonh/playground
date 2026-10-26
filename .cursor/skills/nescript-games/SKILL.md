---
name: nescript-games
description: >-
  Write or change a NEScript game under nescript/examples. Use when adding
  screens, weapons, tables, banks, text, sprites, or CPU logic, and when
  reviewing a NEScript game for brittle patterns. Rampart is the worked example.
---

# NEScript games

Language rules are in `nescript/docs/language-guide.md`. This file is the decisions that guide does not make. Rampart (`nescript/examples/rampart.ne` and `nescript/examples/rampart/`) is the game these rules came from. Match its file split. Do not copy the patterns this file tells you to avoid.

## Write it in NEScript

A game is `.ne` source and nothing else. Do not write a Python, Rust, or shell program that writes `.ne` files, tile art, nametables, or string tables. If NEScript cannot say something, write the data literally in `.ne`, even when it is long, and add the missing feature to [Authoring without generators](../../../nescript/docs/future-work.md#authoring-without-generators) in `nescript/docs/future-work.md`. Use art that comes from an image editor with `@chr("file.png")`, which the compiler reads.

`scripts/gen_rampart.py`, `scripts/rampart_art.py`, and `scripts/gen_platformer_tiles.rs` predate this rule. That plan deletes them. Do not add another, and do not extend them with new kinds of data. Until they are gone, edit them rather than their output.

## Where code goes

UxROM's fixed bank is 16 KB. It holds trampolines, every `const` array, and every function that is not inside `bank`. A `const` array stays in the fixed bank even when only a banked function reads it.

Put `draw` in the state's `on frame`, and keep that state in the fixed bank. Put rules and opponent logic in one `bank`. A cross-bank call costs a trampoline in the fixed bank, so add entry points sparingly.

Include a banked file only from inside that `bank` block. Duplicate includes are skipped and the first include wins. A later include at the top of the program does not move the file. It leaves the first copy where it already was.

When the fixed bank is full, do not add a background. Blank the screen and paint over a nametable you already have. Rampart's setup screen reuses Title for that reason.

## RAM

A banked function may declare locals. Use one. Do not borrow a global as scratch.

`res_a` and `res_b` in Rampart are the outputs of `nudge` and `step_toward`. Do not use them for anything else. A helper that needs two results gets its own named globals, or returns one value.

A function outside a `state` cannot see that state's locals. Data that a banked function and a fixed-bank `on frame` both touch is a global. Say who writes it on the declaration.

A cursor index is only a cursor. Rampart packs "wiping the screen" and "already left" into `cust_cursor` as 10 and 9, and the sprite loop draws only while `cust_cursor < 9`. A new row at 9 would turn the sprites off. Put the mode in its own variable.

## Tables

One id is one index, used by every table for that id. Rampart's weapon id is the shared index of `W_RANGE`, `W_AP`, `W_DMG`, `W_STR`, `WPN_TILE`, `art.WEAPONS`, and `WPN_AT`. The location id is the shared index of `START_ARMOR`, `LOC_STR`, `PLATE`, and the `DEC_*` arrays. Edit the whole set in one change.

Loop to the count const (`NUM_WEAPONS`, `NUM_LOCS`). Do not write the count as a literal. Release builds do not check array bounds. An id past the end reads the next const.

Stock loadouts are indexes into that order (`STOCK_WPN`). There is one writer for a stock loadout. Rampart currently has three copies (CPU setup, the first human, and the next human). Add a weapon by changing the tables and that one writer, not by hunting copies.

Parenthesize a wrap: `(x + NUM_WEAPONS - 1) % NUM_WEAPONS`.

`*`, `/`, and `%` with a value that is not a power of two are software routines. A count of five is fine for a menu. Do not put one inside a per-cell search.

## Bytes on screen

The font is `A-Z`, digits, space, `.`, `:`, and `-`. A letter on screen is an uppercase ASCII byte, and that byte is the tile number. There is no lowercase.

Rampart's strings are in `STRINGS` inside `scripts/gen_rampart.py` until NEScript has `str` (step 3 of the plan). Run the generator after changing them. Do not hand-edit `text.ne`, `assets.ne`, or `backgrounds.ne`. A new game writes its string table in `.ne`.

`FRAME_NAME` is raw ASCII in `constants.ne`. A wrong byte draws a blank tile and nothing warns. Put the intended text in a comment next to each row, as `FRAME_NAME` does, until string-initialized arrays exist.

`put_clear` does not know how long the next string is. The clear width has to be at least the longest string that slot can show. `WPN_NAME_W` is that width for a weapon name. If you lengthen a weapon string, update the width in the same change. A short clear leaves the tail of the previous name up.

`msg_str` advances a cursor and does not clip. A message row is 30 tiles starting at column 1. Add up the pieces, including the space `msg_str` inserts after each one, before you add a word.

Leave columns 0 and 31 empty. TVs and jsnes crop them.

A sprite next to a text row sits at that row times 8, minus 1. Rampart names the setup rows once (`NAME_ROW`, `GUN_ROW`, `ARM_ROW`, `START_ROW` in `constants.ne`), and `cpu.ne` and `customize_state.ne` both derive from them. Do the same for any new row. Two handwritten copies drift.

Eight sprites share a scanline. The ninth is dropped. Count sprites that share a Y before you add one.

## Text entry

Use one of the two layouts NES games settled on. Do not invent a third.

- Rotary letters, for short fixed-width fields such as names and high-score initials: left and right move between letter cells, up and down step the lit cell through space, `A` to `Z`, and back to space. This is the arcade initials screen. Rampart's name field uses it.
- Letter grid, for long or free-form text such as Dragon Warrior or Final Fantasy names and password screens: the alphabet is drawn as a grid, the D-pad moves a cursor over it, `A` adds the letter at the end of the text, and the grid has `BACK` and `END` cells.

In both layouts, `B` is backspace. It erases one letter and steps the cursor left. It never clears the whole field. Start the cursor on the last letter of the default text, the way a text field puts the caret after existing text, so the first `B` erases that letter. Rampart's `name_end()` finds it. Confirming an empty field restores the default name instead of saving a blank one.

Label the controls with the button and the verb: `B BACKSPACE`, `START`. Put the field's label and its value on one row, as `NAME`, `GUN`, and `ARM` are.

This logic lives in Rampart's `cpu.ne` and is not a shared module. NEScript has no library directory yet, and the plan in `nescript/docs/future-work.md` adds one with fonts. Once it exists, move the rotary field there when a second game needs it.

## Sound

Pulse 1 is sound effects. Pulse 2 is music. Noise is footsteps, guns, and impacts. Triangle is a poor thud: an effect's period high byte is fixed at 0, so the lowest note is about A4.

A second `play` on the same channel restarts that channel. Pulse and noise may start on the same frame. Rampart's missile does.

Start the track from the title `on enter`, and stop it when the match ends. A program with no `play`, `start_music`, or `stop_music` links no audio driver.

## Arithmetic that wraps

`u8` subtraction wraps through 255. `save_need` starts at 5 plus armor piercing, then subtracts 1 for cover and 1 for a shield. That stays positive only because of that floor. Another discount wraps, and `unsaved_faces` treats any need above 7 as "no face saves", which is a guaranteed hit. Subtract only after you know the value is large enough.

## The queue and the phase list

`push_cmd` does not check the 64-entry text queue. `head == tail` means empty, including after the tail laps the head, so a dropped paint looks like an idle queue. Flush, or count the commands, before you queue a second full screen.

Rampart's battle `match` ends in `_ => {}`. Do not copy that arm. Handle every phase you add. A forgotten phase should fail the build or draw something impossible to miss, not skip the turn.

## What a weapon means in two places

Charge aims `loadout[actor * 2 + 1]`, the arm slot, with melee saves (no cover, no shield). It does not look at range. `pick_ranged` fires whichever intact mount can reach, gun first, and a range of 1 still fires when the mechs are adjacent. A sword on the gun is a point-blank shot. A gatling cannon on the arm is what Charge swings. If you add a weapon, decide both paths in the same change. There is no melee flag.

## Prove the screen you changed

`tests/emulator` goldens are frame 180 with no buttons. Rampart's golden is the title. It stays green when setup, weapons, or battle are wrong.

Drive the changed screen with `tests/emulator/emu.mjs` (`buttonDown`, `buttonUp`, `runFrames`, `pixels`). One path per rule you changed: the stock row, a wrap around the list, and the screen that shows the result.

After `scripts/gen_rampart.py` or `scripts/rampart_art.py` changes:

```bash
cd nescript
python3 scripts/gen_rampart.py
cargo run --release -- build examples/rampart.ne
sh scripts/pre-commit
```

Commit the generated `.ne` files and the `.nes`.
