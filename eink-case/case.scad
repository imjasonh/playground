// Waveshare 7.5" e-Paper + ESP32 Driver Board case
//
// Devices:
//   - Waveshare 7.5inch e-Paper raw panel (ASIN B075R69T93)
//     outline 170.2 x 111.2 x 1.18 mm, AA 163.2 x 97.92, 24-pin FPC
//   - Waveshare e-Paper ESP32 Driver Board (ASIN B07M5CNP3B)
//     29.46 x 48.25 mm, USB-C (2024+ revisions; Micro-USB earlier)
//     Board has NO mounting holes — retained by a pocket + lid posts.
//
// Printable parts: TWO
//   part="front"  — bezel + panel groove + electronics bay
//   part="back"   — lid
//
// Fasteners:
//   Lid:  4× M2 × 8 mm self-tapping pan-head (into 1.7 mm pilots)
//   Board: none (no holes on the Waveshare PCB). Optional 3M VHB on pocket floor.
//
// Interconnect: the driver-board kit includes an FFC extension cable + adapter.
// With usb_exit="back" or "side" the board sits along a side wall, so use that
// extension (≈33 mm lateral jog from the panel FPC). usb_exit="bottom" puts the
// ZIF nearer the FPC for a shorter path.
//
// Coordinates: X right, Y up (FPC / bottom edge near Y=0), Z toward back.
// Open in OpenSCAD Customizer, or override with -D on the CLI.

/* [Parts] */
part = "assembled";          // [assembled, front, back] Which object to show / export
show_components = true;      // Ghost panel + board in assembled preview
explode = 0;                 // [0:0.5:25] Lid / board separation for assembly views (mm)

/* [Panel — Waveshare 7.5" raw] */
panel_w = 170.2;             // [160:0.1:180] Panel outline width (mm)
panel_h = 111.2;             // [100:0.1:120] Panel outline height (mm)
panel_t = 1.20;              // [0.8:0.05:2] Panel thickness (mm)
active_w = 163.2;            // [150:0.1:170] Active area width (mm)
active_h = 97.92;            // [90:0.01:110] Active area height (mm)
bezel_left = 3.5;            // [2:0.1:8] Left outline→AA bezel (mm)
bezel_right = 3.5;           // [2:0.1:8] Right outline→AA bezel (mm)
bezel_top = 3.40;            // [2:0.1:8] Bezel opposite the FPC edge (mm)
// bezel_fpc derived: panel_h - active_h - bezel_top

/* [FPC / SPI ribbon] */
fpc_w = 14.0;                // [10:0.5:20] FPC width allowance (mm)
fpc_t = 0.35;                // [0.2:0.05:0.6] FPC thickness (mm)
fpc_slot_extra = 4.0;        // [2:0.5:10] Room outside panel edge for the fold (mm)
fpc_channel_w = 22.0;        // [14:1:40] Trough width under panel for FPC + extension (mm)
fpc_channel_len = 55.0;      // [30:5:100] Trough length under panel (mm)

/* [ESP32 driver board] */
board_w = 29.46;             // [25:0.01:40] Board short axis (mm)
board_l = 48.25;             // [40:0.01:60] Board long axis, USB↔ZIF (mm)
board_t = 1.60;              // [1.2:0.1:2.4] PCB thickness (mm)
board_comp_h = 8.0;          // [5:0.5:15] Component clearance above PCB (mm)
usb_w = 9.2;                 // [8:0.1:12] USB-C shell width (mm)
usb_h = 3.6;                 // [3:0.1:5] USB-C shell height (mm)
usb_protrude = 1.5;          // [0.5:0.1:3] USB shell past PCB edge (mm)
board_pocket_clear = 0.5;    // [0.2:0.1:1.2] XY slop in board cradle (mm)

/* [Case geometry] */
wall = 2.4;                  // [1.5:0.1:4] Outer wall thickness (mm)
groove_clearance = 0.40;     // [0.2:0.05:0.8] Slip fit around panel outline (mm)
groove_lip = 1.2;            // [0.8:0.1:2.5] Front bezel lip thickness (mm)
rear_bay_extra = 3.0;        // [1:0.5:8] Extra bay air around board / cable (mm)
lid_thickness = 2.4;         // [1.5:0.1:4] Back lid thickness (mm)
corner_r = 4.0;              // [0:0.5:10] Outer corner radius (mm)
screw_d = 2.4;               // [2:0.1:3.5] Lid screw clearance hole (mm)
screw_boss_d = 7.0;          // [5:0.5:10] Lid screw boss outer diameter (mm)
screw_boss_id = 1.7;         // [1.4:0.1:2.2] M2 self-tap pilot diameter (mm)
use_snaps = true;            // Add lid snap tabs

/* [USB exit] */
usb_exit = "back";           // [back, side, bottom] Perimeter wall for USB-C

/* [Tolerances / print] */
$fn = 48;                    // [16:8:96] Circle segments
eps = 0.02;                  // Boolean overlap fudge (mm)

// ---------------------------------------------------------------------------
// Derived dimensions
// ---------------------------------------------------------------------------
bezel_fpc = panel_h - active_h - bezel_top;

case_outer_w = panel_w + 2 * groove_clearance + 2 * wall;
case_outer_h = panel_h + groove_clearance + fpc_slot_extra + 2 * wall;

window_inset = 0.4;
window_w = active_w - 2 * window_inset;
window_h = active_h - 2 * window_inset;

front_lip_z = groove_lip;
groove_z = panel_t + 2 * groove_clearance;
bay_floor_t = 1.4;
board_standoff_h = 2.0;

// Bay must clear: standoffs + PCB + components + lid-post engagement + air
bay_need = board_standoff_h + board_t + board_comp_h + 2.0;
bay_z = max(bay_need, 12.0) + rear_bay_extra;
front_body_z = front_lip_z + groove_z + bay_z;
total_z = front_body_z + lid_thickness;

panel_x0 = wall + groove_clearance;
panel_y0 = wall + fpc_slot_extra;
active_x0 = panel_x0 + bezel_left;
active_y0 = panel_y0 + bezel_fpc;

board_pose = board_placement();
board_x0 = board_pose[0];
board_y0 = board_pose[1];
board_rot = board_pose[2];
board_z0 = front_lip_z + groove_z + bay_floor_t + board_standoff_h;

// Lid posts hang down from lid underside to just above the PCB top.
lid_post_gap = 0.3; // air above PCB copper
lid_post_h = front_body_z - (board_z0 + board_t) - lid_post_gap;

echo("============================================================");
echo(str("CLOSED OVERALL: ", case_outer_w, " x ", case_outer_h, " x ", total_z, " mm"));
echo(str("  (W x H x D — width along panel long edge, depth front-to-back)"));
echo(str("Printable parts: 2  (front shell + back lid)"));
echo(str("Lid screws: 4 x M2x8mm self-tapping pan head -> ", screw_boss_id, " mm pilots"));
echo(str("Board screws: none (PCB has no holes; pocket + lid posts)"));
echo(str("Panel pocket: ", panel_w + 2 * groove_clearance, " x ", panel_h + groove_clearance, " x ", groove_z, " mm"));
echo(str("Bay depth: ", bay_z, " mm; USB exit: ", usb_exit));
echo(str("FPC-side panel bezel: ", bezel_fpc, " mm; opposite: ", bezel_top, " mm"));
echo("============================================================");

function board_placement() =
    let (
        cx = case_outer_w / 2,
        cy = case_outer_h / 2,
        m = wall + 3.5,
        // Bias toward the FPC edge so the extension run stays short.
        fpc_bias_y = panel_y0 + 18
    )
    usb_exit == "bottom"
        ? [cx - board_w / 2, m + usb_protrude, 90]
    : usb_exit == "side"
        ? [case_outer_w - m - usb_protrude - board_l, max(fpc_bias_y, m), 0]
    : /* back = left / -X wall */ [m + usb_protrude, max(fpc_bias_y, m), 0];

function boss_xy() =
    let (inset = wall + screw_boss_d / 2 + 1.0)
    [
        [inset, inset],
        [case_outer_w - inset, inset],
        [inset, case_outer_h - inset],
        [case_outer_w - inset, case_outer_h - inset]
    ];

function board_corner_xy() =
    board_rot == 90
        ? [
            [board_x0 + 3.5, board_y0 + 3.5],
            [board_x0 + board_w - 3.5, board_y0 + 3.5],
            [board_x0 + 3.5, board_y0 + board_l - 3.5],
            [board_x0 + board_w - 3.5, board_y0 + board_l - 3.5]
          ]
        : [
            [board_x0 + 3.5, board_y0 + 3.5],
            [board_x0 + board_l - 3.5, board_y0 + 3.5],
            [board_x0 + 3.5, board_y0 + board_w - 3.5],
            [board_x0 + board_l - 3.5, board_y0 + board_w - 3.5]
          ];

function board_size_xy() =
    board_rot == 90 ? [board_w, board_l] : [board_l, board_w];

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------
module rounded_rect(w, h, r) {
    rr = min(r, w / 2 - eps, h / 2 - eps);
    if (rr <= 0)
        square([w, h]);
    else
        translate([rr, rr])
            offset(r = rr)
                square([w - 2 * rr, h - 2 * rr]);
}

module rounded_box(w, h, t, r) {
    linear_extrude(height = t)
        rounded_rect(w, h, r);
}

module at_board() {
    translate([board_x0, board_y0, board_z0])
        rotate([0, 0, board_rot])
            children();
}

// ---------------------------------------------------------------------------
// Ghost components (preview only — not in STL parts)
// ---------------------------------------------------------------------------
module panel_ghost() {
    color("Ivory", 0.9)
        translate([panel_x0, panel_y0, front_lip_z + groove_clearance])
            cube([panel_w, panel_h, panel_t]);

    color("#4a4a4a", 0.75)
        translate([active_x0, active_y0, front_lip_z + 0.02])
            cube([active_w, active_h, 0.04]);

    color("#c9a227", 0.95) {
        translate([
            panel_x0 + (panel_w - fpc_w) / 2,
            panel_y0 - fpc_slot_extra - 1,
            front_lip_z + groove_clearance + panel_t * 0.5 - fpc_t * 0.5
        ])
            cube([fpc_w, fpc_slot_extra + 3, fpc_t]);
        translate([
            panel_x0 + (panel_w - fpc_w) / 2,
            panel_y0 + 2,
            front_lip_z + groove_z + bay_floor_t + 0.4
        ])
            cube([fpc_w, fpc_channel_len - 4, fpc_t]);
    }
}

module board_ghost() {
    at_board() {
        color("#1b5e20", 0.92)
            cube([board_l, board_w, board_t]);
        color("#111111", 0.9)
            translate([10, (board_w - 16) / 2, board_t])
                cube([22, 16, 3.2]);
        color("#b0b0b0", 0.95)
            translate([-usb_protrude, (board_w - usb_w) / 2, board_t])
                cube([usb_protrude + 2, usb_w, usb_h]);
        color("#222222", 0.9)
            translate([board_l - 7, (board_w - 16) / 2, board_t])
                cube([6, 16, 2.2]);
    }
}

module usb_cutout() {
    clear = 0.7;
    cw = usb_w + 2 * clear;
    ch = usb_h + 2 * clear;
    deep = wall + usb_protrude + board_l + 8;
    at_board()
        translate([-usb_protrude - wall - 6, (board_w - cw) / 2, board_t - clear])
            cube([deep, cw, ch]);
}

// ---------------------------------------------------------------------------
// Front shell
// ---------------------------------------------------------------------------
module front_shell() {
    difference() {
        union() {
            rounded_box(case_outer_w, case_outer_h, front_body_z, corner_r);

            // Top seating stop (unioned before cuts so it shares volume cleanly)
            translate([
                panel_x0 - groove_clearance,
                panel_y0 + panel_h - eps,
                front_lip_z
            ])
                cube([
                    panel_w + 2 * groove_clearance,
                    wall + groove_clearance,
                    groove_z
                ]);
        }

        // Active-area window
        translate([
            active_x0 + window_inset,
            active_y0 + window_inset,
            -eps
        ])
            cube([window_w, window_h, front_lip_z + 2 * eps]);

        // Panel groove — open at FPC (bottom) edge
        translate([
            panel_x0 - groove_clearance,
            -eps,
            front_lip_z
        ])
            cube([
                panel_w + 2 * groove_clearance,
                panel_y0 + panel_h + groove_clearance + wall,
                groove_z + eps
            ]);

        // Rear electronics bay
        translate([wall, wall, front_lip_z + groove_z])
            rounded_box(
                case_outer_w - 2 * wall,
                case_outer_h - 2 * wall,
                bay_z + eps,
                max(0.2, corner_r - wall)
            );

        // FPC exit through bottom wall (full bay height so the fold can tuck in)
        translate([
            panel_x0 + (panel_w - fpc_channel_w) / 2,
            -eps,
            front_lip_z - eps
        ])
            cube([
                fpc_channel_w,
                wall + fpc_slot_extra + 3,
                groove_z + bay_z + 2 * eps
            ]);

        usb_cutout();

        if (use_snaps) {
            tab_w = 10;
            tab_d = 1.4;
            tab_z = 3.0;
            ys = case_outer_h / 2;
            for (x = [wall - 0.05, case_outer_w - wall - tab_d])
                translate([x, ys - tab_w / 2, front_body_z - tab_z])
                    cube([tab_d + 0.2, tab_w, tab_z + eps]);
        }
    }

    // Bay floor (panel backer) with FPC / extension trough
    difference() {
        translate([wall - eps, wall - eps, front_lip_z + groove_z])
            cube([
                case_outer_w - 2 * wall + 2 * eps,
                case_outer_h - 2 * wall + 2 * eps,
                bay_floor_t
            ]);
        translate([
            panel_x0 + (panel_w - fpc_channel_w) / 2,
            wall - 2 * eps,
            front_lip_z + groove_z - eps
        ])
            cube([
                fpc_channel_w,
                fpc_channel_len,
                bay_floor_t + 2 * eps
            ]);
    }

    // Board cradle walls (PCB has no screw holes)
    board_cradle();

    // Screw bosses for the lid
    for (p = boss_xy())
        translate([p[0], p[1], front_lip_z + groove_z - eps])
            difference() {
                cylinder(d = screw_boss_d, h = bay_z + eps);
                translate([0, 0, -eps])
                    cylinder(d = screw_boss_id, h = bay_z + 3 * eps);
            }
}

module board_cradle() {
    bs = board_size_xy();
    bw = bs[0];
    bh = bs[1];
    wall_h = board_standoff_h + board_t + 0.6;
    t = 1.6;
    z0 = front_lip_z + groove_z + bay_floor_t;

    // Floor pad under the board
    translate([
        board_x0 - board_pocket_clear,
        board_y0 - board_pocket_clear,
        z0
    ])
        cube([
            bw + 2 * board_pocket_clear,
            bh + 2 * board_pocket_clear,
            board_standoff_h
        ]);

    // Low walls on three sides; open toward the FPC trough / ZIF end
    // For rot=0, open on +X (ZIF). For rot=90, open on +Y.
    difference() {
        translate([
            board_x0 - board_pocket_clear - t,
            board_y0 - board_pocket_clear - t,
            z0
        ])
            cube([
                bw + 2 * board_pocket_clear + 2 * t,
                bh + 2 * board_pocket_clear + 2 * t,
                wall_h
            ]);
        // Hollow for PCB
        translate([
            board_x0 - board_pocket_clear,
            board_y0 - board_pocket_clear,
            z0 - eps
        ])
            cube([
                bw + 2 * board_pocket_clear,
                bh + 2 * board_pocket_clear,
                wall_h + 2 * eps
            ]);
        // Open the ZIF / cable side
        if (board_rot == 90) {
            translate([
                board_x0 - board_pocket_clear - t - eps,
                board_y0 + bh - 1,
                z0 - eps
            ])
                cube([
                    bw + 2 * board_pocket_clear + 2 * t + 2 * eps,
                    t + 4,
                    wall_h + 2 * eps
                ]);
        } else {
            translate([
                board_x0 + bw - 1,
                board_y0 - board_pocket_clear - t - eps,
                z0 - eps
            ])
                cube([
                    t + 4,
                    bh + 2 * board_pocket_clear + 2 * t + 2 * eps,
                    wall_h + 2 * eps
                ]);
        }
        // USB end opening
        if (board_rot == 90) {
            translate([
                board_x0 - board_pocket_clear - t - eps,
                board_y0 - board_pocket_clear - t - eps,
                z0 + board_standoff_h
            ])
                cube([
                    bw + 2 * board_pocket_clear + 2 * t + 2 * eps,
                    t + 3,
                    wall_h
                ]);
        } else {
            translate([
                board_x0 - board_pocket_clear - t - eps,
                board_y0 - board_pocket_clear - t - eps,
                z0 + board_standoff_h
            ])
                cube([
                    t + 3,
                    bh + 2 * board_pocket_clear + 2 * t + 2 * eps,
                    wall_h
                ]);
        }
    }
}

// ---------------------------------------------------------------------------
// Back lid
// ---------------------------------------------------------------------------
// Assembly orientation: inner face at z=0 (toward the bay), outer face at
// z=lid_thickness; snap tabs / PCB posts hang into -Z.
// Print orientation (part="back"): flipped so the large outer face sits on
// the bed and the posts/snaps point up.
module back_lid() {
    difference() {
        rounded_box(case_outer_w, case_outer_h, lid_thickness, corner_r);

        for (p = boss_xy())
            translate([p[0], p[1], -eps])
                cylinder(d = screw_d, h = lid_thickness + 2 * eps);

        // Edge notch matching the USB wall cut (not a center window)
        if (usb_exit == "back") {
            clear = 0.7;
            cw = usb_w + 2 * clear;
            usb_cy = board_y0 + (board_rot == 90 ? board_l : board_w) / 2;
            translate([-eps, usb_cy - cw / 2, -eps])
                cube([wall + 6, cw, lid_thickness + 2 * eps]);
        }
    }

    if (use_snaps) {
        tab_w = 9.4;
        tab_d = 1.2;
        tab_z = 2.6;
        ys = case_outer_h / 2;
        for (x = [wall + 0.25, case_outer_w - wall - tab_d - 0.25])
            translate([x, ys - tab_w / 2, -tab_z + eps])
                cube([tab_d, tab_w, tab_z]);
    }

    // Posts that reach down onto the PCB corners (board has no screw holes)
    if (lid_post_h > 0.5)
        for (p = board_corner_xy())
            translate([p[0], p[1], -lid_post_h])
                cylinder(d1 = 3.2, d2 = 2.4, h = lid_post_h);
}

// Flat-outer-down for printing: outer face on z=0, posts/snaps in +Z.
module back_lid_print() {
    translate([0, case_outer_h, lid_thickness])
        rotate([180, 0, 0])
            back_lid();
}

// ---------------------------------------------------------------------------
// Assembly / part switch
// ---------------------------------------------------------------------------
module assembled() {
    color("#3d5a80")
        front_shell();

    translate([0, 0, front_body_z + explode])
        color("#293241")
            back_lid();

    if (show_components) {
        panel_ghost();
        translate([0, 0, explode * 0.35])
            board_ghost();
    }
}

if (part == "assembled")
    assembled();
else if (part == "front")
    front_shell();
else if (part == "back")
    back_lid_print();
