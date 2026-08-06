// Waveshare 7.5" e-Paper + ESP32 Driver Board case
//
// Devices:
//   - Waveshare 7.5inch e-Paper raw panel (ASIN B075R69T93)
//     outline 170.2 x 111.2 x 1.18 mm, AA 163.2 x 97.92, 24-pin FPC
//   - Waveshare e-Paper ESP32 Driver Board (ASIN B07M5CNP3B)
//     29.46 x 48.25 mm, USB-C (2024+). No mounting holes.
//
// THREE printable parts (FDM-friendly — see tools/fdm-design-rules.md):
//   bezel  — flat frame; print outer-face down (pocket opens up)
//   tray   — open bay; print floor-down / cavity up (no mid-air decks)
//   back   — lid; print outer-face down (cradle + snaps open up)
//
// Assembly: panel press-fits into bezel pocket (crush ribs) → clamp bezel
// to tray (Z sandwich) → fold SPI ribbon through the INTERNAL floor slot
// onto the board → lid. No external ribbon hole — cable stays inside.
// Use kit FFC extension for side/back USB.
//
// Panel retention (snug):
//   XY — pocket ≈ panel + panel_clear, plus short crush ribs on L/R/top
//   Z  — tray floor clamps the glass against the bezel window lip
//
// Fasteners:
//   Bezel→tray: 4× M2×8 mm self-tapping (corner pilots)
//   Lid→tray:   4× M2×8 mm self-tapping (same bosses, from the back)
//   Board:      none (cradle + lid posts). Optional VHB under PCB.
//
// Coordinates: X right, Y up (FPC near Y=0), Z toward back.

/* [Parts] */
part = "assembled"; // [assembled, bezel, tray, back] Which object to show / export
show_components = true; // Ghost panel + board in assembled preview
explode = 0;            // [0:0.5:30] Part separation for assembly views (mm)

/* [Panel — Waveshare 7.5" raw] */
panel_w = 170.2;             // [160:0.1:180] Panel outline width (mm)
panel_h = 111.2;             // [100:0.1:120] Panel outline height (mm)
panel_t = 1.20;              // [0.8:0.05:2] Panel thickness (mm)
active_w = 163.2;            // [150:0.1:170] Active area width (mm)
active_h = 97.92;            // [90:0.01:110] Active area height (mm)
bezel_left = 3.5;            // [2:0.1:8] Left outline→AA bezel (mm)
bezel_right = 3.5;           // [2:0.1:8] Right outline→AA bezel (mm)
bezel_top = 3.40;            // [2:0.1:8] Bezel opposite the FPC edge (mm)

/* [FPC / SPI ribbon] */
fpc_w = 14.0;                // [10:0.5:20] FPC width allowance (mm)
fpc_t = 0.35;                // [0.2:0.05:0.6] FPC thickness (mm)
fpc_fold_bay = 6.0;          // [3:0.5:12] Internal bay between wall and panel FPC edge (mm)
fpc_channel_w = 22.0;        // [14:1:40] Internal floor-slot width for the fold (mm)

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
panel_clear = 0.30;          // [0.15:0.05:0.8] Base XY clearance around panel (mm)
panel_crush = 0.20;          // [0:0.05:0.4] Crush-rib intrusion for snug XY (mm)
panel_front_clear = 0.15;    // [0.05:0.05:0.4] Air between window lip and glass (mm)
bezel_face_t = 1.2;          // [0.8:0.1:2.5] Bezel front face thickness (mm)
tray_floor_t = 2.0;          // [1.5:0.1:3] Tray floor (panel backer) thickness (mm)
rear_bay_extra = 3.0;        // [1:0.5:8] Extra bay air (mm)
lid_thickness = 2.4;         // [1.5:0.1:4] Back lid thickness (mm)
corner_r = 4.0;              // [0:0.5:10] Outer corner radius (mm)
screw_d = 2.4;               // [2:0.1:3.5] Screw clearance through bezel/lid (mm)
screw_boss_d = 7.0;          // [5:0.5:10] Boss outer diameter (mm)
screw_boss_id = 1.7;         // [1.4:0.1:2.2] M2 self-tap pilot (mm)
use_snaps = true;            // Lid snap tabs

/* [USB exit] */
usb_exit = "back";           // [back, side, bottom] Perimeter wall for USB-C

/* [Tolerances / print] */
$fn = 48;                    // [16:8:96] Circle segments
eps = 0.02;                  // Boolean overlap fudge (mm)

// ---------------------------------------------------------------------------
// Derived
// ---------------------------------------------------------------------------
bezel_fpc = panel_h - active_h - bezel_top;

// Rim outside the panel must fit M2 bosses without the screws hitting glass.
boss_inset = wall + screw_boss_d / 2 + 1.0;
outer_margin = boss_inset + screw_boss_d / 2 + 0.6; // ≥ ~10.9 mm with defaults

case_outer_w = panel_w + 2 * outer_margin;
case_outer_h = panel_h + fpc_fold_bay + 2 * outer_margin;

window_inset = 0.4;
window_w = active_w - 2 * window_inset;
window_h = active_h - 2 * window_inset;

board_standoff_h = 2.0;
bay_need = board_standoff_h + board_t + board_comp_h + 2.0;
bay_z = max(bay_need, 12.0) + rear_bay_extra;

// Z stack: bezel face → panel → tray floor clamps glass → bay → lid
// Bezel rim top == tray floor bottom == panel back (snug Z clamp).
panel_z0 = bezel_face_t + panel_front_clear;
tray_floor_z0 = panel_z0 + panel_t;
bezel_total_z = tray_floor_z0;       // rim mates with tray floor
bay_z0 = tray_floor_z0 + tray_floor_t;
front_body_z = bay_z0 + bay_z;       // lid mating plane
total_z = front_body_z + lid_thickness;

panel_x0 = outer_margin;
panel_y0 = outer_margin + fpc_fold_bay; // internal fold bay below FPC edge
active_x0 = panel_x0 + bezel_left;
active_y0 = panel_y0 + bezel_fpc;

// Internal floor slot: cable passes from fold bay into rear bay (not outside).
fpc_slot_x0 = panel_x0 + (panel_w - fpc_channel_w) / 2;
fpc_slot_y0 = outer_margin - 1.0;    // still inside outer wall
fpc_slot_y1 = panel_y0 + 10;

board_pose = board_placement();
board_x0 = board_pose[0];
board_y0 = board_pose[1];
board_rot = board_pose[2];
board_z0 = bay_z0 + board_standoff_h;

lid_post_gap = 0.3;
lid_post_h = front_body_z - (board_z0 + board_t) - lid_post_gap;

echo("============================================================");
echo(str("CLOSED OVERALL: ", case_outer_w, " x ", case_outer_h, " x ", total_z, " mm"));
echo("Printable parts: 3  (bezel + tray + back lid)");
echo("Print: bezel face-down | tray cavity-up | lid outer-down");
echo(str("Panel hold: XY clear=", panel_clear, " + crush=", panel_crush,
         "; Z clamp via tray floor"));
echo(str("FPC: internal fold bay ", fpc_fold_bay, " mm; no external ribbon hole"));
echo(str("Lid/bezel screws: M2x8 self-tap -> ", screw_boss_id, " mm pilots"));
echo("Board screws: none (tray cradle + lid posts)");
echo(str("Bay depth: ", bay_z, " mm; USB exit: ", usb_exit));
echo(str("FDM: no AA-spanning decks (see tools/fdm-design-rules.md)"));
echo("============================================================");

function board_placement() =
    let (
        m = wall + 3.5,
        fpc_bias_y = panel_y0 + 18
    )
    usb_exit == "bottom"
        ? [case_outer_w / 2 - board_w / 2, m + usb_protrude, 90]
    : usb_exit == "side"
        ? [case_outer_w - m - usb_protrude - board_l, max(fpc_bias_y, m), 0]
    : /* back */ [m + usb_protrude, max(fpc_bias_y, m), 0];

function boss_xy() =
    [
        [boss_inset, boss_inset],
        [case_outer_w - boss_inset, boss_inset],
        [boss_inset, case_outer_h - boss_inset],
        [case_outer_w - boss_inset, case_outer_h - boss_inset]
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
    if (rr <= 0) square([w, h]);
    else translate([rr, rr]) offset(r = rr) square([w - 2 * rr, h - 2 * rr]);
}

module rounded_box(w, h, t, r) {
    linear_extrude(height = t) rounded_rect(w, h, r);
}

module at_board() {
    translate([board_x0, board_y0, board_z0])
        rotate([0, 0, board_rot])
            children();
}

// ---------------------------------------------------------------------------
// Ghosts
// ---------------------------------------------------------------------------
module panel_ghost() {
    color("Ivory", 0.9)
        translate([panel_x0, panel_y0, panel_z0])
            cube([panel_w, panel_h, panel_t]);
    color("#4a4a4a", 0.75)
        translate([active_x0, active_y0, bezel_face_t - 0.02])
            cube([active_w, active_h, 0.04]);
    // Ribbon stays inside: fold bay → floor slot → rear bay → ZIF
    color("#c9a227", 0.95) {
        translate([
            panel_x0 + (panel_w - fpc_w) / 2,
            panel_y0 - fpc_fold_bay + 0.5,
            panel_z0 + panel_t / 2 - fpc_t / 2
        ])
            cube([fpc_w, fpc_fold_bay + 2, fpc_t]);
        translate([
            panel_x0 + (panel_w - fpc_w) / 2,
            panel_y0 - 2,
            tray_floor_z0 - eps
        ])
            cube([fpc_w, fpc_t + 1, tray_floor_t + 2]);
        translate([
            panel_x0 + (panel_w - fpc_w) / 2,
            panel_y0 + 2,
            bay_z0 + 0.5
        ])
            cube([fpc_w, 40, fpc_t]);
    }
}

module board_ghost() {
    at_board() {
        color("#1b5e20", 0.92) cube([board_l, board_w, board_t]);
        color("#111111", 0.9)
            translate([10, (board_w - 16) / 2, board_t]) cube([22, 16, 3.2]);
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
// Bezel — flat frame, print outer-face down (R1.3)
// Rim top mates with tray floor; panel is Z-clamped between window lip & tray.
// Outer wall is closed. Panel seats on shoulders L/R of a narrow internal
// fold bay; ribbon never exits the case.
// ---------------------------------------------------------------------------
module bezel() {
    pocket_depth = panel_front_clear + panel_t; // rim top = tray floor
    rib_len = 12;
    rib_z0 = bezel_face_t + panel_front_clear;
    rib_h = panel_t * 0.85;
    embed = 0.2;

    union() {
        difference() {
            // Solid blank: face + rim up to tray mating plane
            rounded_box(case_outer_w, case_outer_h, bezel_total_z, corner_r);

            // Active-area window through the face
            translate([
                active_x0 + window_inset,
                active_y0 + window_inset,
                -eps
            ])
                cube([window_w, window_h, bezel_total_z + 3 * eps]);

            // Panel pocket — outline + clear; shoulders remain at FPC edge
            translate([
                panel_x0 - panel_clear,
                panel_y0 - panel_clear,
                bezel_face_t
            ])
                cube([
                    panel_w + 2 * panel_clear,
                    panel_h + 2 * panel_clear,
                    pocket_depth + eps
                ]);

            // Narrow INTERNAL fold bay (outer wall stays closed)
            translate([
                fpc_slot_x0 - 1,
                outer_margin - 1.5,
                bezel_face_t
            ])
                cube([
                    fpc_channel_w + 2,
                    fpc_fold_bay + panel_clear + 3,
                    pocket_depth + eps
                ]);

            // Screw clearances
            for (p = boss_xy())
                translate([p[0], p[1], -eps])
                    cylinder(d = screw_d, h = bezel_total_z + 2 * eps);
        }

        // Crush ribs: local XY interference for a snug press-fit (FDM-friendly).
        // Vertical features — print cleanly. Skip FPC edge (fold bay).
        if (panel_crush > 0) {
            for (yy = [panel_y0 + 20, panel_y0 + panel_h - 20 - rib_len]) {
                translate([panel_x0 - panel_clear - embed, yy, rib_z0])
                    cube([panel_crush + embed, rib_len, rib_h]);
                translate([
                    panel_x0 + panel_w + panel_clear - panel_crush,
                    yy, rib_z0
                ])
                    cube([panel_crush + embed, rib_len, rib_h]);
            }
            for (xx = [panel_x0 + 25, panel_x0 + panel_w - 25 - rib_len])
                translate([
                    xx,
                    panel_y0 + panel_h + panel_clear - panel_crush,
                    rib_z0
                ])
                    cube([rib_len, panel_crush + embed, rib_h]);
        }
    }
}

// ---------------------------------------------------------------------------
// Tray — print floor-down / cavity up (R1.2, R1.3)
// Floor on the bed is the panel backer (solid — not a bridge).
// Internal FPC slot through the floor only — outer wall stays closed.
// ---------------------------------------------------------------------------
module tray() {
    difference() {
        union() {
            // Floor = panel backer (solid plate — prints on bed)
            translate([0, 0, tray_floor_z0])
                rounded_box(case_outer_w, case_outer_h, tray_floor_t, corner_r);

            // Bay walls
            translate([0, 0, bay_z0 - eps])
                difference() {
                    rounded_box(case_outer_w, case_outer_h, bay_z + eps, corner_r);
                    translate([wall, wall, -eps])
                        rounded_box(
                            case_outer_w - 2 * wall,
                            case_outer_h - 2 * wall,
                            bay_z + 3 * eps,
                            max(0.2, corner_r - wall)
                        );
                }
        }

        // Internal ribbon pass-through (floor only — not the outer wall)
        translate([
            fpc_slot_x0,
            fpc_slot_y0,
            tray_floor_z0 - eps
        ])
            cube([
                fpc_channel_w,
                fpc_slot_y1 - fpc_slot_y0,
                tray_floor_t + 2 * eps
            ]);

        // Through-holes for bezel screws (pilots continue in bosses)
        for (p = boss_xy())
            translate([p[0], p[1], tray_floor_z0 - eps])
                cylinder(d = screw_boss_id, h = tray_floor_t + 2 * eps);

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

    // Board cradle on the bay floor (grows UP in print — self-supporting)
    board_cradle();

    // Screw bosses from floor up to lid plane
    for (p = boss_xy())
        translate([p[0], p[1], bay_z0 - eps])
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
    z0 = bay_z0;

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
        // Open ZIF end
        if (board_rot == 90)
            translate([
                board_x0 - board_pocket_clear - t - eps,
                board_y0 + bh - 1,
                z0 - eps
            ])
                cube([
                    bw + 2 * board_pocket_clear + 2 * t + 2 * eps,
                    t + 4, wall_h + 2 * eps
                ]);
        else
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
        // Open USB end
        if (board_rot == 90)
            translate([
                board_x0 - board_pocket_clear - t - eps,
                board_y0 - board_pocket_clear - t - eps,
                z0 + board_standoff_h
            ])
                cube([
                    bw + 2 * board_pocket_clear + 2 * t + 2 * eps,
                    t + 3, wall_h
                ]);
        else
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

// Tray export: floor on bed (shift so tray_floor_z0 → 0)
module tray_print() {
    translate([0, 0, -tray_floor_z0])
        tray();
}

// ---------------------------------------------------------------------------
// Back lid — print outer-face down
// ---------------------------------------------------------------------------
module back_lid() {
    difference() {
        rounded_box(case_outer_w, case_outer_h, lid_thickness, corner_r);

        for (p = boss_xy())
            translate([p[0], p[1], -eps])
                cylinder(d = screw_d, h = lid_thickness + 2 * eps);

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

    if (lid_post_h > 0.5)
        for (p = board_corner_xy())
            translate([p[0], p[1], -lid_post_h])
                cylinder(d1 = 3.2, d2 = 2.4, h = lid_post_h);
}

module back_lid_print() {
    translate([0, case_outer_h, lid_thickness])
        rotate([180, 0, 0])
            back_lid();
}

// ---------------------------------------------------------------------------
// Assembly
// ---------------------------------------------------------------------------
module assembled() {
    color("#3d5a80")
        bezel();

    translate([0, 0, explode])
        color("#4a6fa5")
            tray();

    translate([0, 0, front_body_z + 2 * explode])
        color("#293241")
            back_lid();

    if (show_components) {
        translate([0, 0, explode * 0.4])
            panel_ghost();
        translate([0, 0, explode * 0.7])
            board_ghost();
    }
}

if (part == "assembled")
    assembled();
else if (part == "bezel")
    bezel(); // already face-down printable
else if (part == "tray")
    tray_print();
else if (part == "back")
    back_lid_print();
// Legacy alias
else if (part == "front")
    tray_print();
