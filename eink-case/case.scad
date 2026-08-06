// Waveshare 7.5" e-Paper + ESP32 Driver Board case
//
// Devices:
//   - Waveshare 7.5inch e-Paper raw panel (ASIN B075R69T93)
//     outline 170.2 x 111.2 x 1.2 mm, AA 163.2 x 97.92, 24-pin FPC
//   - Waveshare e-Paper ESP32 Driver Board (ASIN B07M5CNP3B)
//     29.46 x 48.25 mm, USB-C (2024+). No mounting holes.
//
// TWO printable parts — see LEARNINGS.md and tools/fdm-design-rules.md:
//   shell — U-slot + window + backer + bay; print CLOSED-END down (slide open up)
//   cap   — closes FPC end, retains panel; print outer face down
//
// Principle: the panel groove is a U-channel extruded in the print Z
// (slide direction). Every layer is self-supporting — the backer is a
// vertical wall, not a bridge over the window.
//
// Assembly: slide panel into shell from FPC end → fold ribbon into bay →
// seat board → clip cap on (no screws).
//
// Fasteners:
//   Cap→shell: internal cantilever clips (flush outer cap face — no screw heads)
//   Board:     none (cradle + optional VHB)
//
// Assembly coords: X right, Y up (FPC at Y=0), Z toward back.
// Print (shell): closed end (Y=max) on bed, FPC end open at top.

/* [Parts] */
part = "assembled"; // [assembled, shell, cap] Which object to show / export
show_components = true; // Ghost panel + board in assembled preview
explode = 0;            // [0:0.5:40] Part separation for assembly views (mm)

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
fpc_fold_bay = 8.0;          // [4:0.5:14] Internal bay at FPC end before cap (mm)
fpc_channel_w = 22.0;        // [14:1:40] Ribbon pass into board bay (mm)

/* [ESP32 driver board] */
board_w = 29.46;             // [25:0.01:40] Board short axis (mm)
board_l = 48.25;             // [40:0.01:60] Board long axis, USB↔ZIF (mm)
board_t = 1.60;              // [1.2:0.1:2.4] PCB thickness (mm)
board_comp_h = 8.0;          // [5:0.5:15] Component clearance above PCB (mm)
usb_w = 9.2;                 // [8:0.1:12] USB-C shell width (mm)
usb_h = 3.6;                 // [3:0.1:5] USB-C shell height (mm)
usb_protrude = 1.5;          // [0.5:0.1:3] USB shell past PCB edge (mm)
usb_face = 0.0;              // [-1:0.1:1] USB tip vs outer wall (0=flush) (mm)
usb_cut_clear = 0.7;         // [0.3:0.1:1.5] USB cutout clearance (mm)
board_pocket_clear = 0.5;    // [0.2:0.1:1.2] XY slop in board cradle (mm)

/* [Case geometry] */
wall = 2.4;                  // [1.5:0.1:4] Outer wall thickness (mm)
panel_clear = 0.30;          // [0.15:0.05:0.8] Slot clearance around panel (mm)
panel_crush = 0.20;          // [0:0.05:0.4] Crush-rib intrusion in slot (mm)
front_lip_t = 1.4;           // [1.0:0.1:2.5] Front window-lip thickness (mm)
backer_t = 2.0;              // [1.5:0.1:3] Panel backer wall thickness (mm)
rear_bay_extra = 3.0;        // [1:0.5:8] Extra bay air (mm)
cap_t = 2.4;                 // [1.5:0.1:4] Cap thickness along slide axis (mm)
cap_rabbet = 1.2;            // [0.6:0.1:2.5] Cap lip into shell mouth (mm)
cap_skirt = 3.0;             // [1.5:0.5:6] Cap return flange over front/back (mm)
side_rim = 3.0;              // [2:0.1:8] Rim outside panel L/R (mm)
closed_end_wall = 3.0;       // [2:0.1:8] Wall opposite FPC / print bed (mm)

/* [Cap clips — no screws; outer cap face stays flat] */
clip_arm_t = 1.3;            // [1.0:0.1:2.0] Flex-arm thickness (mm)
clip_arm_w = 10.0;           // [6:0.5:16] Flex-arm width along depth (mm)
clip_reach = 6.5;            // [4:0.5:10] Arm length into shell (mm)
clip_barb = 0.9;             // [0.5:0.1:1.4] Barb protrusion into wall (mm)
clip_barb_y = 1.4;           // [0.8:0.1:2.5] Barb catch face length along Y (mm)
clip_clear = 0.25;           // [0.1:0.05:0.5] Pocket clearance (mm)

/* [USB exit] */
usb_exit = "back";           // [back, side] Perimeter wall for USB-C

/* [FDM — elephant-foot relief] */
elephant_chamfer = 0.5;      // [0:0.1:1.5] Bed-face outer chamfer (mm)
window_elephant_chamfer = 0.3; // [0:0.1:1] Window-edge relief on front lip (mm)

/* [Tolerances / print] */
$fn = 48;                    // [16:8:96] Circle segments
eps = 0.02;                  // Boolean overlap fudge (mm)

// ---------------------------------------------------------------------------
// Derived — assembly frame (X right, Y up / FPC at 0, Z toward back)
// ---------------------------------------------------------------------------
bezel_fpc = panel_h - active_h - bezel_top;

slot_t = panel_t + 2 * panel_clear;
// Standoff = printable bead height (≤~1.2 mm fat walls off the backer).
board_standoff = 1.2;
bay_need = board_standoff + board_t + board_comp_h + 2.0;
bay_d = max(bay_need, 12.0) + rear_bay_extra;

z_lip1 = front_lip_t;
z_slot0 = z_lip1;
z_slot1 = z_slot0 + slot_t;
z_backer0 = z_slot1;
z_backer1 = z_backer0 + backer_t;
z_bay0 = z_backer1;
z_bay1 = z_bay0 + bay_d;
case_depth = z_bay1 + wall;

y_open = 0;
y_panel0 = fpc_fold_bay;
y_panel1 = y_panel0 + panel_h;
case_h = y_panel1 + panel_clear + closed_end_wall;

case_w = panel_w + 2 * panel_clear + 2 * side_rim + 2 * wall;
panel_x0 = wall + side_rim + panel_clear;
active_x0 = panel_x0 + bezel_left;
active_y0 = y_panel0 + bezel_fpc;

window_inset = 0.4;
window_x0 = active_x0 + window_inset;
window_y0 = active_y0 + window_inset;
window_w = active_w - 2 * window_inset;
window_h = active_h - 2 * window_inset;

fpc_pass_x0 = panel_x0 + (panel_w - fpc_channel_w) / 2;
fpc_pass_y0 = y_open + 1;
fpc_pass_y1 = y_panel0 + 8;

board_pose = board_placement();
board_x0 = board_pose[0];
board_y0 = board_pose[1];
board_rot = board_pose[2];
board_z0 = z_bay0 + board_standoff;

// Two clip stations per side wall (front-of-bay / back-of-bay), flush windows.
clip_z_pad = 2.0;
function clip_z_list() = [
    z_bay0 + clip_z_pad,
    z_bay1 - clip_z_pad - clip_arm_w
];
clip_catch_y = clip_reach - clip_barb_y - 0.15;

echo("============================================================");
echo(str("CLOSED OVERALL: ", case_w, " x ", case_h + cap_t, " x ", case_depth, " mm"));
echo("Printable parts: 2  (shell + cap)");
echo("Print shell: CLOSED-END down, FPC slide-open UP (U-slot extruded in Z)");
echo("Print cap:   outer face down (FLAT — no screw heads)");
echo(str("Slot: clear=", panel_clear, " crush=", panel_crush,
         "  (panel slides in from FPC end)"));
echo(str("FPC: fold bay ", fpc_fold_bay, " mm; internal backer pass (no external hole)"));
echo(str("Cap retention: 4× internal clips (barb ", clip_barb, " mm); no screws"));
echo("Board screws: none (bay cradle, connected to backer)");
echo(str("Bay depth: ", bay_d, " mm; USB exit: ", usb_exit,
         "  tip@", usb_exit == "side" ? case_w - usb_face : usb_face, " mm"));
echo(str("Board standoff/beads: ", board_standoff, " mm (rails fused to backer)"));
echo(str("Elephant-foot chamfer: ", elephant_chamfer, " mm"));
echo("See LEARNINGS.md — U-slot print-upward principle");
echo("============================================================");

// Board sits near the CLOSED end so cradle features grow UP in print Z.
// USB exits a perimeter wall in XY (PCB is parallel to the backer, so the
// connector cannot point out the rear Z face).
//   usb_exit=back → left wall (X=0), board_rot=0, USB at local -X
//   usb_exit=side → right wall (X=case_w), board_rot=180, USB at world +X
function board_placement() =
    let (
        m = wall + 3.5,
        // rot 0/180 keeps board_w along Y
        by = case_h - wall - m - board_w - 2,
        y0 = max(m, by)
    )
    usb_exit == "side"
        // Origin at ZIF end after 180°; USB tip at x = board_x0 + usb_protrude.
        ? [case_w - usb_face - usb_protrude, y0 + board_w, 180]
    : /* back */ [usb_face + usb_protrude, y0, 0];

function board_size_xy() =
    // Axis-aligned footprint in assembly XY (accounts for 180°).
    [board_l, board_w];

function board_footprint() =
    let (sz = board_size_xy())
        usb_exit == "side"
            ? [board_x0 - sz[0], board_y0 - sz[1], sz[0], sz[1]]
        : /* back */ [board_x0, board_y0, sz[0], sz[1]];

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------
module rounded_rect(w, h, r) {
    rr = min(r, w / 2 - eps, h / 2 - eps);
    if (rr <= 0) square([w, h]);
    else translate([rr, rr]) offset(r = rr) square([w - 2 * rr, h - 2 * rr]);
}

module bottom_outer_chamfer_cut(w, h, r, ch) {
    if (ch > 0)
        difference() {
            translate([-eps, -eps, -eps])
                cube([w + 2 * eps, h + 2 * eps, ch + eps]);
            hull() {
                translate([0, 0, ch])
                    linear_extrude(height = eps)
                        rounded_rect(w, h, r);
                translate([ch, ch, -eps])
                    linear_extrude(height = eps)
                        rounded_rect(
                            max(eps, w - 2 * ch),
                            max(eps, h - 2 * ch),
                            max(0.01, r - ch)
                        );
            }
        }
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
        translate([panel_x0, y_panel0, z_slot0 + panel_clear])
            cube([panel_w, panel_h, panel_t]);
    color("#4a4a4a", 0.75)
        translate([active_x0, active_y0, -0.02])
            cube([active_w, active_h, 0.04]);
    color("#c9a227", 0.95) {
        translate([
            panel_x0 + (panel_w - fpc_w) / 2,
            y_open + 1,
            z_slot0 + panel_clear + panel_t / 2 - fpc_t / 2
        ])
            cube([fpc_w, y_panel0 + 2, fpc_t]);
        translate([
            panel_x0 + (panel_w - fpc_w) / 2,
            y_panel0 + 2,
            z_bay0 + 0.5
        ])
            cube([fpc_w, 36, fpc_t]);
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
    // Tunnel sized to the USB-C shell, in board-local frame (works for rot 0/180).
    cw = usb_w + 2 * usb_cut_clear;
    ch = usb_h + 2 * usb_cut_clear;
    // Reach from well outside the outer wall, past the connector, into the bay.
    deep = wall + abs(usb_face) + usb_protrude + 10;
    at_board()
        translate([
            -usb_protrude - wall - abs(usb_face) - 4,
            (board_w - cw) / 2,
            board_t - usb_cut_clear
        ])
            cube([deep, cw, ch]);

    // PCB edge relief where the board overlaps the perimeter wall thickness.
    fp = board_footprint();
    bx = fp[0];
    by = fp[1];
    bw = fp[2];
    bh = fp[3];
    if (usb_exit == "back")
        translate([-eps, by - board_pocket_clear, board_z0 - 0.15])
            cube([
                max(wall, usb_face + usb_protrude) + 2 * eps,
                bh + 2 * board_pocket_clear,
                board_t + 0.3
            ]);
    else if (usb_exit == "side")
        translate([
            case_w - max(wall, usb_face + usb_protrude) - eps,
            by - board_pocket_clear,
            board_z0 - 0.15
        ])
            cube([
                max(wall, usb_face + usb_protrude) + 2 * eps,
                bh + 2 * board_pocket_clear,
                board_t + 0.3
            ]);
}

// ---------------------------------------------------------------------------
// Cap clips (internal cantilever — outer cap face stays flat)
// ---------------------------------------------------------------------------
// side = -1 (left wall) or +1 (right wall). Arm flexes in X; barb snaps into
// a flush through-window in the side wall. 45° lead-in is print-up safe on
// the cap (outer face down → arm grows in +Z_print).
module cap_side_clip(side, z0) {
    x_arm = side < 0
        ? wall + clip_clear
        : case_w - wall - clip_arm_t - clip_clear;
    translate([x_arm, -eps, z0]) {
        cube([clip_arm_t, clip_reach + eps, clip_arm_w]);
        // Catch face + 45° insertion ramp (barb points outward)
        y_catch = clip_reach - clip_barb_y;
        if (side < 0) {
            translate([-clip_barb, y_catch, 0])
                cube([clip_barb + eps, clip_barb_y, clip_arm_w]);
            hull() {
                translate([0, y_catch - clip_barb, 0])
                    cube([eps, eps, clip_arm_w]);
                translate([0, y_catch, 0])
                    cube([eps, eps, clip_arm_w]);
                translate([-clip_barb, y_catch, 0])
                    cube([eps, eps, clip_arm_w]);
            }
        } else {
            translate([clip_arm_t - eps, y_catch, 0])
                cube([clip_barb + eps, clip_barb_y, clip_arm_w]);
            hull() {
                translate([clip_arm_t - eps, y_catch - clip_barb, 0])
                    cube([eps, eps, clip_arm_w]);
                translate([clip_arm_t - eps, y_catch, 0])
                    cube([eps, eps, clip_arm_w]);
                translate([clip_arm_t + clip_barb - eps, y_catch, 0])
                    cube([eps, eps, clip_arm_w]);
            }
        }
    }
}

module shell_clip_windows() {
    // Flush side windows — barb seats flush; pinch to release. No proud heads.
    for (z0 = clip_z_list())
        for (x = [-eps, case_w - wall - eps])
            translate([
                x,
                clip_catch_y - clip_clear,
                z0 - clip_clear
            ])
                cube([
                    wall + 2 * eps,
                    clip_barb_y + 2 * clip_clear,
                    clip_arm_w + 2 * clip_clear
                ]);
}

// ---------------------------------------------------------------------------
// Shell
// ---------------------------------------------------------------------------
module shell() {
    difference() {
        cube([case_w, case_h, case_depth]);

        // Window through front lip
        translate([window_x0, window_y0, -eps])
            cube([window_w, window_h, z_slot0 + eps]);

        if (window_elephant_chamfer > 0)
            hull() {
                translate([
                    window_x0 - window_elephant_chamfer,
                    window_y0 - window_elephant_chamfer,
                    -eps
                ])
                    cube([
                        window_w + 2 * window_elephant_chamfer,
                        window_h + 2 * window_elephant_chamfer,
                        eps
                    ]);
                translate([window_x0, window_y0, window_elephant_chamfer])
                    cube([window_w, window_h, eps]);
            }

        // U-slot (panel groove) — open at FPC end, stopped by closed-end wall.
        // Front lip stays SOLID through the fold-bay strip so the front never
        // shows bay innards; the panel end-loads under the continuous lip.
        translate([
            panel_x0 - panel_clear,
            y_open - eps,
            z_slot0
        ])
            cube([
                panel_w + 2 * panel_clear,
                y_panel1 + panel_clear - y_open + eps,
                slot_t
            ]);

        // Electronics bay
        translate([wall, wall, z_bay0])
            cube([case_w - 2 * wall, case_h - 2 * wall, bay_d + eps]);

        // Bay access through the open-end wall (board + ribbon during assembly).
        // Fully covered by the cap plug when closed — not a front-face hole.
        translate([wall, y_open - eps, z_bay0])
            cube([case_w - 2 * wall, wall + 2 * eps, bay_d + eps]);

        // Perimeter rabbet on the open-end face for the cap lip (hides seam)
        if (cap_rabbet > 0)
            difference() {
                translate([-eps, y_open - eps, -eps])
                    cube([case_w + 2 * eps, cap_rabbet + eps, case_depth + 2 * eps]);
                translate([cap_rabbet, y_open - 2 * eps, cap_rabbet])
                    cube([
                        case_w - 2 * cap_rabbet,
                        cap_rabbet + 3 * eps,
                        case_depth - 2 * cap_rabbet
                    ]);
            }

        // Internal ribbon pass through backer into bay
        translate([
            fpc_pass_x0,
            fpc_pass_y0,
            z_backer0 - eps
        ])
            cube([
                fpc_channel_w,
                fpc_pass_y1 - fpc_pass_y0,
                backer_t + 2 * eps
            ]);

        shell_clip_windows();
        usb_cutout();
    }

    // Crush ribs in the slot (vertical beads along print Z after reorient)
    if (panel_crush > 0) {
        rib_len = 14;
        rib_z = z_slot0 + panel_clear;
        rib_h = panel_t * 0.85;
        for (yy = [y_panel0 + 18, y_panel0 + panel_h - 18 - rib_len]) {
            translate([panel_x0 - panel_clear - 0.15, yy, rib_z])
                cube([panel_crush + 0.15, rib_len, rib_h]);
            translate([
                panel_x0 + panel_w + panel_clear - panel_crush,
                yy, rib_z
            ])
                cube([panel_crush + 0.15, rib_len, rib_h]);
        }
    }

    board_cradle();
}

module board_cradle() {
    // Print-up safe: PCB plane parallel to backer (vertical wall in print).
    // Rails/stops are constant-X / constant-Y walls fused to the backer at
    // z_bay0 — not floating, not horizontal shelves (R1.2).
    // USB end is left open (no rail) so the connector can reach the wall.
    fp = board_footprint();
    bx = fp[0];
    by = fp[1];
    bw = fp[2];
    bh = fp[3];
    t = 1.6;
    clear = board_pocket_clear;
    // Overlap the backer by eps so CGAL unions (coplanar touch ≠ merge)
    rail_z0 = z_bay0 - eps;
    rail_z1 = board_z0 + board_t + 0.9;
    rail_h = rail_z1 - rail_z0;
    groove_z = board_t + 0.2;

    module rail_with_groove(x, groove_from_right = false) {
        difference() {
            translate([x, by - clear, rail_z0])
                cube([t, bh + 2 * clear, rail_h]);
            // PCB edge groove — retains through-thickness without a shelf
            gx = groove_from_right ? x - 0.2 : x + t - (t * 0.55);
            translate([gx, by - clear - eps, board_z0])
                cube([t * 0.55 + 0.3, bh + 2 * clear + 2 * eps, groove_z]);
        }
    }

    // Long-side rail opposite the USB wall only
    if (usb_exit == "back")
        rail_with_groove(bx + bw + clear, false);
    else
        rail_with_groove(bx - clear - t, true);

    // Closed-end stop (high-Y) — fused to backer; low-Y stays open for insert
    translate([bx - clear - (usb_exit == "back" ? 0 : t), by + bh + clear, rail_z0])
        cube([
            bw + 2 * clear + t,
            t,
            rail_h
        ]);

    // Standoff beads on the backer — height matches board_z0 exactly
    for (yy = [by + 5, by + bh - 9])
        for (xx = [bx + 8, bx + bw - 12])
            if (xx > wall + 1 && xx + 4 < case_w - wall - 1)
                translate([xx, yy, z_bay0 - eps])
                    cube([4, 4, board_standoff + eps]);
}

module shell_print() {
    // Closed end on bed, FPC mouth up — U-slot extruded in print Z
    translate([0, 0, case_h])
        rotate([-90, 0, 0])
            difference() {
                shell();
                if (elephant_chamfer > 0)
                    translate([0, case_h + eps, 0])
                        rotate([90, 0, 0])
                            bottom_outer_chamfer_cut(
                                case_w, case_depth, 0.01, elephant_chamfer
                            );
            }
}

// ---------------------------------------------------------------------------
// Cap
// ---------------------------------------------------------------------------
module cap() {
    // Outer end plate — full flat face (no screw holes / proud heads)
    translate([0, -cap_t, 0])
        cube([case_w, cap_t, case_depth]);

    // Perimeter lip into the shell rabbet (tight visual seam)
    if (cap_rabbet > 0)
        difference() {
            translate([0.1, -eps, 0.1])
                cube([case_w - 0.2, cap_rabbet, case_depth - 0.2]);
            translate([cap_rabbet + 0.05, -2 * eps, cap_rabbet + 0.05])
                cube([
                    case_w - 2 * cap_rabbet - 0.1,
                    cap_rabbet + 3 * eps,
                    case_depth - 2 * cap_rabbet - 0.1
                ]);
        }

    // Return skirts over front + back — joint not visible from those faces
    if (cap_skirt > 0) {
        translate([0, -eps, -0.02])
            cube([case_w, cap_skirt, front_lip_t + 0.02]);
        translate([0, -eps, case_depth - wall - 0.02])
            cube([case_w, cap_skirt, wall + 0.04]);
    }

    // Retention tongue into the U-slot — butts the panel's FPC edge so the
    // glass cannot slide back into the fold bay / out the mouth.
    // Center notch leaves the ribbon path clear into the backer pass.
    tongue_len = y_panel0 - 0.2;
    difference() {
        translate([
            panel_x0 - panel_clear + 1,
            -eps,
            z_slot0 + 0.05
        ])
            cube([
                panel_w + 2 * panel_clear - 2,
                tongue_len,
                slot_t - 0.1
            ]);
        translate([
            fpc_pass_x0 - 0.5,
            -2 * eps,
            z_slot0 - eps
        ])
            cube([
                fpc_channel_w + 1,
                tongue_len + 3 * eps,
                slot_t + 2 * eps
            ]);
    }

    // Bay plug — fills the end-wall access so you can't see the PCB.
    // Inset from the side walls so it doesn't collide with the clip arms.
    plug_inset = clip_arm_t + clip_clear + 0.4;
    translate([wall + plug_inset, -eps, z_bay0 + 0.25])
        cube([
            case_w - 2 * wall - 2 * plug_inset,
            wall + 0.35,
            bay_d - 0.5
        ]);

    // Four internal clips (2 per side) — latch into flush side windows
    for (z0 = clip_z_list()) {
        cap_side_clip(-1, z0);
        cap_side_clip(+1, z0);
    }
}

module cap_print() {
    // Outer face (y = -cap_t) on bed; thickness builds in +Z.
    // Rx(90): (x,y,z) -> (x,-z,y). Shift y by +cap_t first so outer → y=0 → z_print=0.
    translate([0, case_depth, 0])
        rotate([90, 0, 0])
            translate([0, cap_t, 0])
                difference() {
                    cap();
                    if (elephant_chamfer > 0)
                        translate([0, -cap_t - eps, 0])
                            rotate([-90, 0, 0])
                                bottom_outer_chamfer_cut(
                                    case_w, case_depth, 0.01, elephant_chamfer
                                );
                }
}

// ---------------------------------------------------------------------------
// Assembly
// ---------------------------------------------------------------------------
module assembled() {
    color("#3d5a80")
        shell();

    translate([0, -explode, 0])
        color("#293241")
            cap();

    if (show_components) {
        translate([0, -explode * 0.35, 0])
            panel_ghost();
        translate([0, -explode * 0.15, 0])
            board_ghost();
    }
}

if (part == "assembled")
    assembled();
else if (part == "shell")
    shell_print();
else if (part == "cap")
    cap_print();
else if (part == "bezel" || part == "tray" || part == "front")
    shell_print(); // legacy aliases
else if (part == "back")
    cap_print();
