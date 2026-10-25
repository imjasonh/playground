// war/compare.ne — card rank/suit extraction and round resolution.
//
// Cards are packed as `(rank << 4) | suit`; the extractors are
// one shift or one mask each.

inline fun card_rank(card: u8) -> u8 {
    return card >> 4
}

inline fun card_suit(card: u8) -> u8 {
    return card & 0x0F
}

// Compare two cards by rank. Returns:
//     1 if A wins, 2 if B wins, 0 if they tie.
fun compare_cards(a: u8, b: u8) -> u8 {
    var ra: u8 = card_rank(a)
    var rb: u8 = card_rank(b)
    if ra > rb {
        return 1
    }
    if rb > ra {
        return 2
    }
    return 0
}
