// rampart/result.ne: who won, and the game-over message.

fun total_armor(p: u8) -> u8 {
    var s: u8 = 0
    var l: u8 = 0
    while l < NUM_LOCS {
        s += armor[p * 11 + l]
        l += 1
    }
    return s
}

// 0 or 1 for a winner, 2 for a draw. Uses res_a and res_b.
fun decide_winner() -> u8 {
    if crits[0] >= LOSS_CRITS {
        if crits[1] >= LOSS_CRITS {
            return 2
        }
        return 1
    }
    if crits[1] >= LOSS_CRITS {
        return 0
    }
    if crits[0] < crits[1] {
        return 0
    }
    if crits[1] < crits[0] {
        return 1
    }
    res_a = total_armor(0)
    res_b = total_armor(1)
    if res_a > res_b {
        return 0
    }
    if res_b > res_a {
        return 1
    }
    return 2
}

fun game_over() {
    stop_music
    res_a = decide_winner()
    msg_clear()
    msg_line(MSG_ROW1)
    if crits[0] >= LOSS_CRITS and crits[1] >= LOSS_CRITS {
        msg_str(S_BOTH)
    } else if crits[1] >= LOSS_CRITS {
        msg_who(1)
        msg_str(S_WRECKED)
    } else if crits[0] >= LOSS_CRITS {
        msg_who(0)
        msg_str(S_WRECKED)
    } else {
        msg_str(S_TIME_UP)
    }
    msg_line(MSG_ROW2)
    if res_a == 2 {
        msg_str(S_DRAW)
    } else {
        msg_who(res_a)
        msg_str(S_WINS)
    }
    msg_str(S_PRESS_START)
    over_timer = 0
    phase = P_OVER
}
