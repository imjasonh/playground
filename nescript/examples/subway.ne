// NYC Subway: walk the platforms and ride the trains of the New York
// City subway, with weekday stops, running times, and headways from
// the MTA's GTFS feed.

game "NYC Subway" {
    mapper: MMC3
    mirroring: vertical
}

include "subway/data_header.ne"
include "subway/gfx_consts.ne"
include "subway/gfx_chr.ne"
include "subway/globals.ne"

// The two-tone door chime, played when the doors open.
sfx DoorChime {
    duty: 2
    pitch: [0xA8, 0xA8, 0xA8, 0xA8, 0xA8, 0xA8, 0xA8, 0xA8, 0xA8, 0xA8, 0xA8, 0xA8, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5, 0xD5]
    volume: [12, 11, 10, 10, 9, 9, 8, 8, 7, 7, 6, 6, 12, 11, 10, 9, 9, 8, 8, 7, 7, 6, 6, 5, 5, 4, 4, 3, 3, 3, 2, 2, 2, 1, 1, 0]
}

// espeak-ng en-us at 150 words per minute, "Stand clear of the closing doors.",
// resampled to DMC rate 11.
dpcm StandClear {
    rate: 11
    data: @binary("subway/stand_clear.dmc")
}

bank Stations {
    include "subway/data_stations.ne"
    include "subway/stations.ne"
}

bank Lines {
    include "subway/data_lines.ne"
    include "subway/lines.ne"
}

bank Gfx {
    include "subway/gfx_screens.ne"
    include "subway/screens.ne"
    include "subway/band.ne"
    include "subway/scenery.ne"
}

bank Map {
    include "subway/gfx_map.ne"
    include "subway/map.ne"
    include "subway/pause_map.ne"
}

bank Sim {
    include "subway/platform_logic.ne"
    include "subway/riding_logic.ne"
}

include "subway/video.ne"
include "subway/hud.ne"
include "subway/platform_state.ne"
include "subway/riding_state.ne"
include "subway/pause_state.ne"

start Platform
