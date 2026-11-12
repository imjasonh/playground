# Clash quick reference

A simultaneous-bidding game for 2 to 4 players. Full rules in [`rules.md`](rules.md).

## What you need

- A standard deck with the four Aces removed: 48 cards in four suits — Intelligence, Strength, Speed, Ingenuity.
- Cards are worth their number; Jack is 11, Queen 12, King 13. The Aces are only Home markers.

## Setup

- 1 to 4 human players fill the rest of the table with bots, for 2 to 4 players total.
- Each player and bot takes a suit — its **Home** — and keeps that Ace face up as a marker.
- Split the shuffled 48 cards evenly, so everyone holds the same stack (24 / 16 / 12 cards at 2 / 3 / 4 players).
- Each human takes 4 cards into a hand, then splits the rest of their stack into two equal face-down piles: a **draw pile** and an **ante pile**.
- A bot needs no hand: stack its 4 cards and draw pile into one face-down **bid pile**, and leave its ante pile face down like everyone else's.

## Each clash

- Everyone flips the top card of their ante pile into the middle, face up. Together these are the **pot**.
- Everyone bids one card at once:
  - humans choose 1 card from their hand and play it face down;
  - bots just flip the top card of their bid pile and play it.
- Reveal together. Your **bid** is your card's value, plus 1 for each card of your suit already in the pot, plus 1 more if the card you played is your suit.
- The highest bid wins and takes the pot into their winnings. The card you played is spent either way — set it aside; you never win it back and it never returns to your hand.
- A tie for the top wins nothing: leave the pot in place and it joins the next clash's antes. It can carry more than once.
- Humans refill their hand back to 4 from their draw pile, and the next clash begins.

## Winning

- The game ends when the ante piles run out: a fixed 10 / 6 / 4 clashes at 2 / 3 / 4 players.
- Add up the values of the cards you won. The most wins; a tie shares the victory.

## Longer games

- Shuffle 2 or more decks together for a longer game; set the extra Aces aside and deal exactly as above.
- Each deck adds to the ante pile, so clashes scale with it:

| Players | 1 deck | 2 decks | 3 decks | 4 decks |
| --- | --- | --- | --- | --- |
| 2 | 10 | 22 | 34 | 46 |
| 3 | 6 | 14 | 22 | 30 |
| 4 | 4 | 10 | 16 | 22 |
