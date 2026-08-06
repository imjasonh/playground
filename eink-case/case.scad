// Waveshare 7.5" e-Paper + ESP32 Driver Board case
//
// Devices:
//   - Waveshare 7.5inch e-Paper raw panel (ASIN B075R69T93)
//     outline 170.2 x 111.2 x 1.18 mm, AA 163.2 x 97.92, 24-pin FPC
//   - Waveshare e-Paper ESP32 Driver Board (ASIN B07M5CNP3B)
//     29.46 x 48.25 mm, USB-C (2024+ revisions; Micro-USB earlier)
//
// Assembly:
//   1. Slide the panel into the three-sided groove from the FPC edge until
//      it seats against the top stop (left / right / top lips hold it).
//   2. Fold the SPI FPC 180° under the panel into the rear bay.
//   3. Seat the ESP32 board in the rear bay; USB exits the chosen wall.
//   4. Snap / screw the back lid on.
//
// Coordinates: X right, Y up (FPC / bottom edge near Y=0), Z toward back.
// Open in OpenSCAD Customizer, or override with -D on the CLI.

/* [Parts] */
part = "assembled"; // [assembled, front, back]
show_components = true;
explode = 0; // [0:0.5:25]

/* [Panel — Waveshare 7.5" raw] */
panel_w = 170.2;
panel_h = 111.2;
panel_t = 1.20;
active_w = 163.2;
active_h = 97.92;
// Distance from outline edges to active area (FPC exits the bottom / -Y edge).
bezel_left = 3.5;
bezel_right = 3.5;
bezel_top = 3.40; // edge opposite the FPC
// bezel_fpc is derived: panel_h - active_h - bezel_top

/* [FPC / SPI ribbon] */
fpc_w = 14.0;       // 24-pin @ 0.5 mm pitch, with margin
fpc_t = 0.35;
fpc_slot_extra = 2.5;

/* [ESP32 driver board] */
board_w = 29.46;    // short axis
board_l = 48.25;    // long axis (USB on one short end)
board_t = 1.60;
board_comp_h = 6.5; // tallest parts above PCB
usb_w = 9.2;
usb_h = 3.4;
usb_protrude = 1.5;

/* [Case geometry] */
wall = 2.2;
groove_clearance = 0.35;  // slip fit around panel outline
groove_lip = 1.1;         // front lip retaining the glass over the AA edge
rear_bay_extra = 2.5;
lid_thickness = 2.2;
corner_r = 4.0;
screw_d = 2.4;            // M2 clearance through lid
screw_boss_d = 6.5;
screw_boss_id = 1.7;      // pilot for self-tapping M2
use_snaps = true;

/* [USB exit] */
// Perimeter wall the USB-C cable leaves through (board is oriented to match).
// "back" = left (-X) wall of the case (rear-cable routing along the wall).
usb_exit = "back"; // [back, side, bottom]

/* [Tolerances / print] */
$fn = 48;
eps = 0.02;

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
bay_floor_t = 1.2;
bay_z = max(board_t + board_comp_h + 1.0, 10.0) + rear_bay_extra;
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
board_standoff_h = 1.8;
board_z0 = front_lip_z + groove_z + bay_floor_t + board_standoff_h;

echo(str("Case outer: ", case_outer_w, " x ", case_outer_h, " x ", total_z, " mm"));
echo(str("Panel bezel FPC-side ", bezel_fpc, " / top ", bezel_top, " mm"));
echo(str("Bay depth ", bay_z, " mm; USB exit: ", usb_exit));

// [x, y, rot_z] — board corner; rot 0 => local +X along case +X, USB at local -X.
function board_placement() =
    let (
        cx = case_outer_w / 2,
        cy = case_outer_h / 2,
        m = wall + 3
    )
    usb_exit == "bottom"
        ? [cx - board_w / 2, m + usb_protrude, 90]
    : usb_exit == "side"
        ? [case_outer_w - m - usb_protrude - board_l, cy - board_w / 2, 0]
    : /* back */ [m + usb_protrude, cy - board_w / 2, 0];

function boss_xy() =
    let (inset = wall + screw_boss_d / 2 + 0.8)
    [
        [inset, inset],
        [case_outer_w - inset, inset],
        [inset, case_outer_h - inset],
        [case_outer_w - inset, case_outer_h - inset]
    ];

function board_corner_xy() =
    board_rot == 90
        ? [
            [board_x0 + 4, board_y0 + 4],
            [board_x0 + board_w - 4, board_y0 + 4],
            [board_x0 + 4, board_y0 + board_l - 4],
            [board_x0 + board_w - 4, board_y0 + board_l - 4]
          ]
        : [
            [board_x0 + 4, board_y0 + 4],
            [board_x0 + board_l - 4, board_y0 + 4],
            [board_x0 + 4, board_y0 + board_w - 4],
            [board_x0 + board_l - 4, board_y0 + board_w - 4]
          ];

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
// Ghost components (preview)
// ---------------------------------------------------------------------------
module panel_ghost() {
    color("Ivory", 0.9)
        translate([panel_x0, panel_y0, front_lip_z + groove_clearance])
            cube([panel_w, panel_h, panel_t]);

    color("#4a4a4a", 0.75)
        translate([active_x0, active_y0, front_lip_z + 0.02])
            cube([active_w, active_h, 0.04]);

    color("#c9a227", 0.95) {
        // stub out the FPC edge
        translate([
            panel_x0 + (panel_w - fpc_w) / 2,
            panel_y0 - fpc_slot_extra - 1,
            front_lip_z + groove_clearance + panel_t * 0.5 - fpc_t * 0.5
        ])
            cube([fpc_w, fpc_slot_extra + 3, fpc_t]);
        // folded under into the bay
        translate([
            panel_x0 + (panel_w - fpc_w) / 2,
            panel_y0 + 4,
            front_lip_z + groove_z + 0.8
        ])
            cube([fpc_w, 28, fpc_t]);
    }
}

module board_ghost() {
    at_board() {
        color("#1b5e20", 0.92)
            cube([board_l, board_w, board_t]);
        color("#111111", 0.9)
            translate([10, (board_w - 16) / 2, board_t])
                cube([22, 16, 3.0]);
        color("#b0b0b0", 0.95)
            translate([-usb_protrude, (board_w - usb_w) / 2, board_t])
                cube([usb_protrude + 2, usb_w, usb_h]);
        color("#222222", 0.9)
            translate([board_l - 6, (board_w - 16) / 2, board_t])
                cube([5, 16, 2.0]);
    }
}

module usb_cutout() {
    // Punch from well outside the case through the USB wall and past the shell.
    clear = 0.6;
    cw = usb_w + 2 * clear;
    ch = usb_h + 2 * clear;
    deep = wall + usb_protrude + board_l;
    at_board()
        translate([-usb_protrude - wall - 4, (board_w - cw) / 2, board_t - clear])
            cube([deep, cw, ch]);
}

// ---------------------------------------------------------------------------
// Front shell
// ---------------------------------------------------------------------------
module front_shell() {
    difference() {
        rounded_box(case_outer_w, case_outer_h, front_body_z, corner_r);

        // Active-area window
        translate([
            active_x0 + window_inset,
            active_y0 + window_inset,
            -eps
        ])
            cube([window_w, window_h, front_lip_z + 2 * eps]);

        // Panel groove — open at the FPC (bottom) edge for slide-in
        translate([
            panel_x0 - groove_clearance,
            -eps,
            front_lip_z
        ])
            cube([
                panel_w + 2 * groove_clearance,
                panel_y0 + panel_h + groove_clearance + eps,
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

        // FPC exit through bottom wall
        translate([
            panel_x0 + (panel_w - fpc_w) / 2 - fpc_slot_extra,
            -eps,
            front_lip_z - 0.2
        ])
            cube([
                fpc_w + 2 * fpc_slot_extra,
                wall + fpc_slot_extra + 2,
                groove_z + bay_z + 1
            ]);

        usb_cutout();

        // Female snap recesses
        if (use_snaps) {
            tab_w = 10;
            tab_d = 1.3;
            tab_z = 2.8;
            ys = case_outer_h / 2;
            for (x = [wall - 0.1, case_outer_w - wall - tab_d])
                translate([x, ys - tab_w / 2, front_body_z - tab_z])
                    cube([tab_d + 0.25, tab_w, tab_z + eps]);
        }
    }

    // Top seating stop — panel slides in until it hits this rib
    translate([
        panel_x0 - groove_clearance,
        panel_y0 + panel_h,
        front_lip_z
    ])
        cube([
            panel_w + 2 * groove_clearance,
            max(0.8, wall - groove_clearance),
            groove_z
        ]);

    // Bay floor behind the panel (panel back rests here; FPC fold channel cut out)
    difference() {
        translate([wall, wall, front_lip_z + groove_z])
            cube([
                case_outer_w - 2 * wall,
                case_outer_h - 2 * wall,
                bay_floor_t
            ]);
        // Channel for folded FPC under the panel
        translate([
            panel_x0 + (panel_w - fpc_w) / 2 - fpc_slot_extra,
            wall - eps,
            front_lip_z + groove_z - eps
        ])
            cube([
                fpc_w + 2 * fpc_slot_extra,
                panel_y0 + 40,
                bay_floor_t + 2 * eps
            ]);
    }

    // Board standoffs on the bay floor
    for (p = board_corner_xy())
        translate([p[0], p[1], front_lip_z + groove_z + bay_floor_t])
            difference() {
                cylinder(d = 4.5, h = board_standoff_h);
                translate([0, 0, -eps])
                    cylinder(d = 1.4, h = board_standoff_h + 2 * eps);
            }

    // Screw bosses
    for (p = boss_xy())
        translate([p[0], p[1], front_lip_z + groove_z])
            difference() {
                cylinder(d = screw_boss_d, h = bay_z);
                translate([0, 0, -eps])
                    cylinder(d = screw_boss_id, h = bay_z + 2 * eps);
            }
}

// ---------------------------------------------------------------------------
// Back lid
// ---------------------------------------------------------------------------
module back_lid() {
    standoff = 1.6;
    difference() {
        rounded_box(case_outer_w, case_outer_h, lid_thickness, corner_r);

        for (p = boss_xy())
            translate([p[0], p[1], -eps])
                cylinder(d = screw_d, h = lid_thickness + 2 * eps);

        // Edge notch matching the USB wall cut when exit is "back"
        if (usb_exit == "back") {
            clear = 0.6;
            cw = usb_w + 2 * clear;
            usb_cy = board_y0 + board_w / 2;
            translate([-eps, usb_cy - cw / 2, -eps])
                cube([wall + 5, cw, lid_thickness + 2 * eps]);
        }

        // Recessed label pad
        translate([
            case_outer_w / 2 - 22,
            case_outer_h / 2 - 7,
            lid_thickness - 0.35
        ])
            cube([44, 14, 0.5]);
    }

    // Male snap tabs
    if (use_snaps) {
        tab_w = 9.4;
        tab_d = 1.15;
        tab_z = 2.5;
        ys = case_outer_h / 2;
        for (x = [wall + 0.2, case_outer_w - wall - tab_d - 0.2])
            translate([x, ys - tab_w / 2, -tab_z])
                cube([tab_d, tab_w, tab_z + eps]);
    }

    // Short posts that kiss PCB corners
    for (p = board_corner_xy())
        translate([p[0], p[1], -standoff])
            cylinder(d = 2.6, h = standoff);
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
    back_lid();
