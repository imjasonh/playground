// keep/audio.ne: the gunshot. Pulse effects and the music are the
// built-in set (shoot, hit, damage, error, title, battle, win,
// gameover). Noise is the shot, so it can start on the same frame
// as a pulse effect.

sfx Gun {
    channel: noise
    pitch: 2
    volume: [15, 12, 8, 5, 2]
}
