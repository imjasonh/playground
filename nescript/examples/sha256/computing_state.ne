// sha256/computing_state.ne — runs the SHA-256 block compression.
//
// The compression is split across frames so the main loop keeps
// responding to the NMI handshake. Each frame advances one
// "phase"; every phase does a batch of 4 iterations so the
// whole compression (48 schedule steps + 64 rounds + fold)
// finishes inside ~30 frames — roughly half a second of
// wall-clock wait between pressing Enter and the hash appearing.
//
// Phase map:
//     0..11   schedule W[16..63] in batches of 4 (12 × 4 = 48)
//     12..27  rounds 0..63        in batches of 4 (16 × 4 = 64)
//     28      fold wk[A..H] into h_state, transition to Showing

const SCHED_PHASES:  u8 = 12               // 12 × 4 = 48 schedule steps
const ROUND_PHASES:  u8 = 16               // 16 × 4 = 64 rounds
const FOLD_PHASE:    u8 = 28               // SCHED + ROUND
const BATCH_SIZE:    u8 = 4                // iterations per frame

state Computing {
    on enter {
        // Reset persistent hash state and build the padded
        // block from the user's message. Phased work then runs
        // on top of the freshly-initialised w[] / h_state /
        // wk[A..H].
        reset_hash_state()
        build_padded_block()
        init_abcdefgh()

        cp_phase = 0
    }

    on frame {
        if cp_phase < SCHED_PHASES {
            // Each schedule phase handles BATCH_SIZE words. The
            // schedule_one / round_one APIs both want a byte
            // offset (= word_index * 4), so track that directly
            // instead of recomputing `index << 2` per iteration:
            // the byte offset is just incremented by 4 in lieu
            // of the index by 1.
            //
            // First byte offset for this phase: (16 + phase*4)*4
            // = 64 + phase * 16.
            var w_byte: u8 = 64 + (cp_phase << 4)
            var step: u8 = 0
            while step < BATCH_SIZE {
                schedule_one(w_byte)
                w_byte += 4
                step += 1
            }
            cp_phase += 1
        } else if cp_phase < FOLD_PHASE {
            // Round batch. First byte offset for this phase:
            // (phase - SCHED_PHASES) * 4 * 4
            // = (phase - SCHED_PHASES) << 4.
            var kw_byte: u8 = (cp_phase - SCHED_PHASES) << 4
            var step2: u8 = 0
            while step2 < BATCH_SIZE {
                round_one(kw_byte)
                kw_byte += 4
                step2 += 1
            }
            cp_phase += 1
        } else {
            // Fold a..h into h_state and hand off to Showing.
            fold_abcdefgh()
            transition Showing
        }

        // Draw the input buffer so the user can see what they
        // typed while the hash is being computed. The cursor
        // sprite is deliberately not drawn here — the keyboard
        // is inactive during this phase.
        draw_input()
    }
}
