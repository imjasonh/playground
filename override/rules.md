# OVERRIDE — v2 (locked)

**Players:** 1, 2, or 3  
**Deck:** standard 52-card deck (no jokers)  
**Objective:** capture the most cards in your Score Pile.

## Factions and cycle

Three real factions form a dominance cycle. A fourth suit is neutral:

| Suit | Role |
| --- | --- |
| Intelligence | Beats Strength |
| Strength | Beats Speed |
| Speed | Beats Intelligence |
| Ingenuity | Mercenary — not in the cycle |

Ingenuity never wins or loses a **Direct Counter**. It competes only on rank in a **Standoff**.

## Ranks (Ace low)

| Card | Value |
| --- | --- |
| Ace | 1 (lowest) |
| 2–10 | Face value |
| Jack (Bronze) | 11 |
| Queen (Silver) | 12 |
| King (Gold) | 13 (highest) |

## Home suit

Each seat prefers one distinct real faction as its **Home suit**. Ingenuity cannot be a Home suit. Cards are still dealt at random from one shared deck.

When you play a Home-suit card:

1. **Rank boost (+3):** add 3 to that card’s rank in every rank comparison (Standoff, War, and tie-breaking among winning-suit cards in a Direct Counter).
2. **Reinforcement:** if you **win** the Clash with a Home-suit card, capture one extra card from the top of the center deck into your Score Pile. Skip if the deck is empty.

The +3 never beats a Direct Counter. Rule 1 (suit) always overrides Rule 2 (rank).

## Modes (always three seats)

| Mode | Seats |
| --- | --- |
| 3-player | Three humans; each picks a different Home suit |
| 2-player | Two humans plus one random-hand bot (bot takes the leftover Home suit) |
| 1-player | One human plus two random-hand bots |

A **random-hand bot** holds five cards like everyone else and plays a random legal card each Clash. Ingenuity’s thirteen cards are ownerless and dealt at random into any hand.

## A Clash

1. **Select:** each player with cards chooses one card face-down (mandatory if you hold a card).
2. **Reveal:** flip simultaneously (solo: flip bot cards when revealed).
3. **Resolve:** apply the resolution hierarchy. The winner places every played card face-down in their Score Pile.
4. **Replenish:** draw from the center deck until your hand holds five cards again.

## Resolution hierarchy

Count **distinct real suits** on the table (ignore Ingenuity). The count is always 0, 1, 2, or 3.

### 1. Direct Counter (exactly two distinct real suits)

The suit that wins the cycle takes the Clash. If only one player played that suit, they win.

If multiple players played the winning suit, the highest **effective rank** among those cards wins (apply Home +3). **If those effective ranks tie, declare War** among the tied players (same procedure as a Standoff tie).

The losing real suit and all Ingenuity cards are out of contention for this Clash.

### 2. Standoff (zero, one, or three distinct real suits)

Ignore suits. The highest effective rank on the **entire table** wins, including Ingenuity.

### 3. War (Standoff or Direct Counter rank tie)

When players tie at the top effective rank:

1. Tied players stay in the War. Other players are knocked out; their cards remain in the pot.
2. Each tied player places one card face-down into the pot (burned), then reveals a second card.
3. Resolve the revealed cards with this same hierarchy. The winner takes the whole pot.
4. If the revealed cards tie again, repeat.

**War backstops:**

| Hand size | Action |
| --- | --- |
| 2+ cards | Burn one face-down, reveal one for fighting |
| 1 card | Reveal it as your fighter (no burn) |
| 0 cards | Drop out of the War; your committed cards stay in the pot |

If exactly one tied player can still fight, they win the pot. If every tied player is empty, split the pot as evenly as possible; any odd card goes to the seat with the highest already-revealed rank in that War.

## Endgame

When the center deck is empty, keep playing until hands are empty. If only one player still holds cards, set those leftovers aside **unscored** (nothing left to clash against).

The player with the most cards in their Score Pile wins. Ties on the final count are shared wins.
