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
// seat board → snap/screw cap on.
//
// Fasteners:
//   Cap→shell: 2× M2×8 mm self-tapping (open-end bosses) + snaps
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
board_pocket_clear = 0.5;    // [0.2:0.1:1.2] XY slop in board cradle (mm)

/* [Case geometry] */
wall = 2.4;                  // [1.5:0.1:4] Outer wall thickness (mm)
panel_clear = 0.30;          // [0.15:0.05:0.8] Slot clearance around panel (mm)
panel_crush = 0.20;          // [0:0.05:0.4] Crush-rib intrusion in slot (mm)
front_lip_t = 1.4;           // [1.0:0.1:2.5] Front window-lip thickness (mm)
backer_t = 2.0;              // [1.5:0.1:3] Panel backer wall thickness (mm)
rear_bay_extra = 3.0;        // [1:0.5:8] Extra bay air (mm)
cap_t = 2.4;                 // [1.5:0.1:4] Cap thickness along slide axis (mm)
side_rim = 3.0;              // [2:0.1:8] Rim outside panel L/R (mm)
closed_end_wall = 3.0;       // [2:0.1:8] Wall opposite FPC / print bed (mm)
screw_d = 2.4;               // [2:0.1:3.5] Screw clearance through cap (mm)
screw_boss_d = 7.0;          // [5:0.5:10] Boss outer diameter (mm)
screw_boss_id = 1.7;         // [1.4:0.1:2.2] M2 self-tap pilot (mm)
use_snaps = true;            // Cap snap tabs

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
board_standoff = 2.0;
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

boss_y = wall + screw_boss_d / 2 + 0.5;
function boss_xy() = [
    [wall + screw_boss_d / 2 + 0.5, boss_y],
    [case_w - wall - screw_boss_d / 2 - 0.5, boss_y]
];

echo("============================================================");
echo(str("CLOSED OVERALL: ", case_w, " x ", case_h + cap_t, " x ", case_depth, " mm"));
echo("Printable parts: 2  (shell + cap)");
echo("Print shell: CLOSED-END down, FPC slide-open UP (U-slot extruded in Z)");
echo("Print cap:   outer face down");
echo(str("Slot: clear=", panel_clear, " crush=", panel_crush,
         "  (panel slides in from FPC end)"));
echo(str("FPC: fold bay ", fpc_fold_bay, " mm; internal backer pass (no external hole)"));
echo(str("Cap screws: 2× M2x8 self-tap -> ", screw_boss_id, " mm pilots + snaps"));
echo("Board screws: none (bay cradle)");
echo(str("Bay depth: ", bay_d, " mm; USB exit: ", usb_exit));
echo(str("Elephant-foot chamfer: ", elephant_chamfer, " mm"));
echo("See LEARNINGS.md — U-slot print-upward principle");
echo("============================================================");

// Board sits near the CLOSED end so its cradle grows UP in print (from the
// bed-side bay floor). Horizontal shelves off the backer are forbidden (R1.2).
function board_placement() =
    let (
        m = wall + 3.5,
        // Board long axis along X when usb_exit=back; place near closed end.
        by = case_h - wall - m - (usb_exit == "side" ? board_l : board_w) - 2
    )
    usb_exit == "side"
        ? [case_w - m - usb_protrude - board_l, max(m, by), 0]
    : /* back */ [m + usb_protrude, max(m, by), 0];

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
    clear = 0.7;
    cw = usb_w + 2 * clear;
    ch = usb_h + 2 * clear;
    deep = wall + usb_protrude + board_l + 8;
    at_board()
        translate([-usb_protrude - wall - 6, (board_w - cw) / 2, board_t - clear])
            cube([deep, cw, ch]);
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

        // U-slot (panel groove) — open at FPC end, stopped by closed-end wall
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

        // Open the front lip at the FPC mouth so the panel can enter the U
        translate([
            panel_x0 - panel_clear,
            y_open - eps,
            -eps
        ])
            cube([
                panel_w + 2 * panel_clear,
                max(eps, y_panel0 - y_open + panel_clear),
                z_slot0 + eps
            ]);

        // Electronics bay (open at FPC end under the cap)
        translate([wall, wall, z_bay0])
            cube([case_w - 2 * wall, case_h - 2 * wall, bay_d + eps]);
        translate([wall, y_open - eps, z_bay0])
            cube([case_w - 2 * wall, wall + 2 * eps, bay_d + eps]);

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

        // Cap screw pilots (along +Y into open-end bosses)
        for (p = boss_xy())
            translate([p[0], y_open - eps, z_bay0 + bay_d / 2])
                rotate([-90, 0, 0])
                    cylinder(d = screw_boss_id, h = 22);

        usb_cutout();

        if (use_snaps) {
            tab_d = 1.4;
            tab_len = 3.0;
            for (x = [wall - 0.05, case_w - wall - tab_d])
                translate([x, y_open - eps, z_bay1 - tab_len])
                    cube([tab_d + 0.2, 3.5, tab_len + eps]);
        }
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

    // Cap bosses along +Y (become upright columns when shell is print-oriented)
    boss_len = 16;
    for (p = boss_xy())
        translate([p[0], y_open + wall - eps, z_bay0 + bay_d / 2])
            rotate([-90, 0, 0])
                difference() {
                    cylinder(d = screw_boss_d, h = boss_len);
                    translate([0, 0, -eps])
                        cylinder(d = screw_boss_id, h = boss_len + 2 * eps);
                }

    board_cradle();
}

module board_cradle() {
    // Print-up safe: PCB plane is parallel to the backer (vertical in print).
    // Side rails = walls of constant X (vertical). End stops = walls of
    // constant Y near the closed end (also vertical after reorient).
    // No shelves growing out of the backer in +Z.
    bs = board_size_xy();
    bw = bs[0];
    bh = bs[1];
    t = 1.6;
    rail_z0 = z_bay0 + 1.0;
    rail_z1 = board_z0 + board_t + 0.8;
    rail_h = rail_z1 - rail_z0;

    // Left / right rails (constant X → vertical walls in print)
    for (x = [
        board_x0 - board_pocket_clear - t,
        board_x0 + bw + board_pocket_clear
    ])
        translate([x, board_y0 - board_pocket_clear, rail_z0])
            cube([t, bh + 2 * board_pocket_clear, rail_h]);

    // Closed-end stop (constant Y near case_h → vertical wall in print)
    translate([
        board_x0 - board_pocket_clear - t,
        board_y0 + bh + board_pocket_clear,
        rail_z0
    ])
        cube([bw + 2 * board_pocket_clear + 2 * t, t, rail_h]);

    // Thin standoff beads on the backer (≤1.2 mm — printable as fat walls,
    // not a deck) so the PCB sits off the backer face.
    bead = min(board_standoff, 1.2);
    for (yy = [board_y0 + 4, board_y0 + bh - 8])
        for (xx = [board_x0 + 6, board_x0 + bw - 10])
            translate([xx, yy, z_bay0])
                cube([4, 4, bead]);
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
    difference() {
        translate([0, -cap_t, 0])
            cube([case_w, cap_t, case_depth]);

        for (p = boss_xy())
            translate([p[0], -cap_t - eps, z_bay0 + bay_d / 2])
                rotate([-90, 0, 0])
                    cylinder(d = screw_d, h = cap_t + 2 * eps);
    }

    // Retention tongue into the U-slot mouth
    translate([
        panel_x0 - panel_clear + 1,
        -eps,
        z_slot0
    ])
        cube([
            panel_w + 2 * panel_clear - 2,
            2.2,
            slot_t
        ]);

    if (use_snaps) {
        tab_d = 1.2;
        tab_len = 2.6;
        for (x = [wall + 0.25, case_w - wall - tab_d - 0.25])
            translate([x, -eps, z_bay1 - tab_len])
                cube([tab_d, 2.4, tab_len]);
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
