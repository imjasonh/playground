// Waveshare 7.5" e-Paper + ESP32 Driver Board case
//
// Devices:
//   - Waveshare 7.5inch e-Paper raw panel (ASIN B075R69T93)
//     outline 170.2 x 111.2 x 1.2 mm, AA 163.2 x 97.92, 24-pin FPC
//   - Waveshare e-Paper ESP32 Driver Board (ASIN B07M5CNP3B)
//     29.46 x 48.25 mm, USB-C (2024+). No mounting holes.
//
// TWO printable parts — see LEARNINGS.md and tools/fdm-design-rules.md:
//   shell — U-slot + window lattice + backer + bay; print CLOSED-END down
//   cap   — closes FPC end, retains panel; print outer face down
//
// Principle: the panel groove is a U-channel extruded in the print Z
// (slide direction). Every layer is self-supporting — the backer is a
// vertical wall, not a bridge over the window.
//
// Assembly: slide panel into shell from FPC end → connect ribbon → slide the
// board ZIF-end-first into straight rails → seat cap → insert two rigid keys.
//
// Fasteners:
//   Cap→shell: two rigid printed side keys (PLA-safe; no flex, no screws)
//   Board:     none (straight slide-in cradle; cap retains it)
//
// Assembly coords: X right, Y up (FPC at Y=0), Z toward back.
// Print (shell): closed end (Y=max) on bed, FPC end open at top.

/* [Parts] */
part = "assembled"; // [assembled, shell, cap, key] Which object to show / export
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
usb_face = 0.0;              // [0:0.1:2] USB recess from cap outer face (mm)
usb_cut_clear = 0.7;         // [0.3:0.1:1.5] USB cutout clearance (mm)
board_pocket_clear = 0.75;   // [0.4:0.05:1.2] PCB edge/rail clearance (mm)
board_z_clear = 0.30;        // [0.15:0.05:0.6] PCB thickness clearance (mm)
board_edge_capture = 1.0;    // [0.6:0.1:1.5] PCB edge held by each rail (mm)
board_end_clear = 0.30;      // [0.1:0.05:0.8] End play between cap/stop (mm)

/* [Case geometry] */
wall = 2.4;                  // [1.5:0.1:4] Outer wall thickness (mm)
panel_clear = 0.40;          // [0.2:0.05:0.8] Slot clearance around panel (mm)
panel_crush = 0.15;          // [0:0.05:0.4] Crush-rib intrusion in slot (mm)
front_lip_t = 1.4;           // [1.0:0.1:2.5] Front window-lip thickness (mm)
backer_t = 2.0;              // [1.5:0.1:3] Panel backer wall thickness (mm)
rear_bay_extra = 3.0;        // [1:0.5:8] Extra bay air (mm)
cap_t = 2.4;                 // [1.5:0.1:4] Cap thickness along slide axis (mm)
cap_rabbet = 1.2;            // [0.6:0.1:2.5] Cap lip into shell mouth (mm)
cap_skirt = 3.0;             // [1.5:0.5:6] Cap return flange over front/back (mm)
side_rim = 1.5;              // [1.2:0.1:8] Rim outside panel L/R (mm)
closed_end_wall = 3.0;       // [2:0.1:8] Wall opposite FPC / print bed (mm)

/* [Cap locks — rigid printed keys; PLA-safe, no bending] */
lock_tongue_t = 2.0;         // [1.5:0.1:3] Cap side-tongue thickness (mm)
lock_reach = 8.0;            // [6:0.5:12] Tongue reach into shell (mm)
lock_key_y = 2.6;            // [2:0.1:4] Key shear thickness along case Y (mm)
lock_key_z = 7.0;            // [5:0.5:10] Key body height (mm)
lock_key_clear = 0.25;       // [0.15:0.05:0.5] Key/slot clearance (mm)
lock_wedge = 0.10;           // [0:0.05:0.3] Full-seat wedge interference (mm)
lock_head_t = 1.2;           // [0.8:0.1:2] Side pull-tab projection (mm)
lock_head_y = 5.2;           // [4:0.2:8] Pull-tab width (mm)
lock_head_z = 10.0;          // [8:0.5:14] Pull-tab height (mm)
lock_tip = 0.8;              // [0.4:0.1:1.5] Insertion lead-in length (mm)

/* [USB exit] */
usb_exit = "cap";            // [cap] USB-C exits through removable cap

/* [FDM — elephant-foot relief] */
elephant_chamfer = 0.3;      // [0:0.1:1.5] Bed-face outer chamfer (mm)
window_elephant_chamfer = 0.3; // [0:0.1:1] Window-edge relief on front lip (mm)

/* [FDM — sacrificial support for the 162 mm window lintel] */
window_bridge_supports = true; // Built-in removable support lattice
bridge_support_count = 6;     // [3:1:10] Vertical breakaway columns
bridge_support_w = 1.2;       // [0.8:0.1:2] Main column width (mm)
bridge_support_neck = 0.45;   // [0.4:0.05:0.8] Snap-off neck width (mm)
bridge_support_neck_len = 1.2; // [0.6:0.1:2] Neck taper height (mm)
bridge_support_gap = 0.20;    // [0:0.05:0.4] Gap below lintel (one 0.2 layer)
bridge_support_setback = 0.25; // [0:0.05:0.6] Recess from cosmetic face (mm)
bridge_tie_h = 0.8;           // [0.4:0.1:1.2] Two stabilizer rows (mm)

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

lock_key_center_y = 4.8;
lock_key_center_z = z_bay0 + bay_d / 2;
lock_key_body_l = wall + lock_key_clear + lock_tongue_t + 0.8;

assert(panel_clear > panel_crush,
       "panel_clear must exceed panel_crush so the glass can slide");
assert(case_w <= 180,
       "Default shell must fit the Bambu A1 Mini's 180 mm X dimension");
assert(lock_key_center_y + lock_key_y / 2 + lock_key_clear < lock_reach,
       "Rigid key slot must remain inside the cap lock tongue");
assert(!window_bridge_supports ||
       (bridge_support_count >= 1 &&
        bridge_support_neck <= bridge_support_w &&
        bridge_support_setback < front_lip_t),
       "Window bridge-support dimensions are invalid");

echo("============================================================");
echo(str("CLOSED OVERALL: ", case_w, " x ", case_h + cap_t, " x ", case_depth, " mm"));
echo("Printable geometries: 3  (shell + cap + key; print 2 keys)");
echo("Print shell: CLOSED-END down, FPC slide-open UP (U-slot extruded in Z)");
echo("Print cap:   outer face down (flat; USB opening only)");
echo(str("Slot: clear=", panel_clear, " crush=", panel_crush,
         " effective rib clearance/side=", panel_clear - panel_crush));
echo(str("FPC: fold bay ", fpc_fold_bay, " mm; internal backer pass (no external hole)"));
echo(str("Cap retention: 2× rigid printed keys; clearance=", lock_key_clear,
         " mm; wedge=", lock_wedge, " mm (PLA-safe, no flex)"));
echo(str("Board: ZIF-end-first straight slide; edge clear=", board_pocket_clear,
         " mm; thickness clear=", board_z_clear, " mm"));
echo(str("USB: cap opening ", usb_w + 2 * usb_cut_clear, " x ",
         usb_h + 2 * usb_cut_clear, " mm; face recess=", usb_face, " mm"));
echo(str("Board standoff: ", board_standoff, " mm; rails fused to backer"));
echo(str("Window lintel support: ",
         window_bridge_supports ? bridge_support_count : 0,
         " breakaway columns; max bridge≈",
         window_bridge_supports
            ? window_w / (bridge_support_count + 1) - bridge_support_w
            : window_w,
         " mm; Z gap=", bridge_support_gap, " mm"));
echo(str("Elephant-foot chamfer: ", elephant_chamfer, " mm"));
echo("See LEARNINGS.md — U-slot print-upward principle");
echo("============================================================");

// Board rotates so its long axis follows the shell's insertion direction.
// The ZIF end leads into two straight grooves; USB remains at the cap mouth.
// Local -X (USB) maps to world -Y (the removable-cap end).
function board_placement() =
    [
        case_w / 2 + board_w / 2,
        -cap_t + usb_face + usb_protrude,
        90
    ];

function board_size_xy() =
    [board_w, board_l];

function board_footprint() =
    [board_x0 - board_w, board_y0, board_w, board_l];

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

module cap_usb_cutouts() {
    // USB tunnel through the cap at final display resolution / placement.
    cw = usb_w + 2 * usb_cut_clear;
    ch = usb_h + 2 * usb_cut_clear;
    at_board()
        translate([
            -usb_protrude - usb_face - eps,
            (board_w - cw) / 2,
            board_t - usb_cut_clear
        ])
            cube([
                usb_protrude + usb_face + cap_t + 4,
                cw,
                ch
            ]);

    // The PCB's USB edge sits partly inside the cap. Recess only the cap's
    // inner face; the outer face remains solid except for the USB tunnel.
    fp = board_footprint();
    bx = fp[0];
    by = fp[1];
    bw = fp[2];
    relief_y0 = min(by - board_end_clear, -eps);
    translate([
        bx - board_pocket_clear,
        relief_y0,
        board_z0 - board_z_clear
    ])
        cube([
            bw + 2 * board_pocket_clear,
            -relief_y0 + eps,
            board_t + 2 * board_z_clear
        ]);
}

// ---------------------------------------------------------------------------
// PLA-safe cap locks — two rigid printed keys, no cantilever flex
// ---------------------------------------------------------------------------
module shell_lock_slots() {
    hole_y = lock_key_y + 2 * lock_key_clear;
    hole_z = lock_key_z + 2 * lock_key_clear;
    for (x = [-eps, case_w - wall - eps])
        translate([
            x,
            lock_key_center_y - hole_y / 2,
            lock_key_center_z - hole_z / 2
        ])
            cube([wall + 2 * eps, hole_y, hole_z]);
}

module cap_lock_tongues() {
    tongue_z0 =
        lock_key_center_z - lock_key_z / 2 - lock_key_clear - 1.0;
    tongue_h = lock_key_z + 2 * lock_key_clear + 2.0;
    difference() {
        union() {
            translate([
                wall + lock_key_clear,
                -eps,
                tongue_z0
            ])
                cube([lock_tongue_t, lock_reach + eps, tongue_h]);
            translate([
                case_w - wall - lock_key_clear - lock_tongue_t,
                -eps,
                tongue_z0
            ])
                cube([lock_tongue_t, lock_reach + eps, tongue_h]);
        }
        translate([
            -eps,
            lock_key_center_y - lock_key_y / 2 - lock_key_clear,
            lock_key_center_z - lock_key_z / 2 - lock_key_clear
        ])
            cube([
                case_w + 2 * eps,
                lock_key_y + 2 * lock_key_clear,
                lock_key_z + 2 * lock_key_clear
            ]);
    }
}

module lock_key() {
    body_end = lock_key_body_l - lock_tip;
    seated_y =
        lock_key_y + 2 * lock_key_clear + lock_wedge;
    union() {
        // Pull tab remains on the side of the case, not its standing end.
        translate([
            -lock_head_t,
            -lock_head_y / 2,
            -lock_head_z / 2
        ])
            cube([
                lock_head_t + eps,
                lock_head_y,
                lock_head_z
            ]);

        // Shallow self-locking wedge: easy lead-in, then 0.10 mm nominal
        // interference at full seat. The whole wall/tongue pair takes the
        // tiny compliance; there is no thin PLA flexure to snap.
        hull() {
            translate([
                0,
                -seated_y / 2,
                -lock_key_z / 2
            ])
                cube([eps, seated_y, lock_key_z]);
            translate([
                body_end - eps,
                -lock_key_y / 2,
                -lock_key_z / 2
            ])
                cube([eps, lock_key_y, lock_key_z]);
        }

        // Rigid lead-in taper; insertion requires no bending.
        hull() {
            translate([
                body_end - eps,
                -lock_key_y / 2,
                -lock_key_z / 2
            ])
                cube([eps, lock_key_y, lock_key_z]);
            translate([
                lock_key_body_l - eps,
                -lock_key_y / 2 + 0.35,
                -lock_key_z / 2 + 0.35
            ])
                cube([
                    eps,
                    lock_key_y - 0.7,
                    lock_key_z - 0.7
                ]);
        }
    }
}

module lock_key_at(side, pull = 0) {
    if (side < 0)
        translate([
            -pull,
            lock_key_center_y,
            lock_key_center_z
        ])
            lock_key();
    else
        translate([
            case_w + pull,
            lock_key_center_y,
            lock_key_center_z
        ])
            mirror([1, 0, 0])
                lock_key();
}

module lock_key_print() {
    // Largest head face on bed; rigid body grows upward.
    translate([
        lock_head_z / 2,
        lock_head_y / 2,
        lock_head_t
    ])
        rotate([0, -90, 0])
            lock_key();
}

module window_bridge_lattice() {
    // In shell print orientation, assembly Y becomes print Z. The window's
    // upper lintel would otherwise begin as one ~162 mm unsupported line.
    // These sacrificial Y-columns turn it into short bridges. They attach only
    // at the window's lower edge through narrow necks; a one-layer top gap
    // lets the lintel land on them without strongly welding to them.
    wy_top = window_y0;
    wy_bottom = window_y0 + window_h;
    y_top = wy_top + bridge_support_gap;
    y_neck = wy_bottom - bridge_support_neck_len;
    support_z0 = bridge_support_setback;
    support_depth = front_lip_t - bridge_support_setback;
    first_x =
        window_x0 + window_w / (bridge_support_count + 1);
    last_x =
        window_x0 +
        bridge_support_count * window_w /
        (bridge_support_count + 1);

    for (i = [1 : bridge_support_count]) {
        cx =
            window_x0 +
            i * window_w / (bridge_support_count + 1);

        // Main removable column
        translate([
            cx - bridge_support_w / 2,
            y_top,
            support_z0
        ])
            cube([
                bridge_support_w,
                y_neck - y_top + eps,
                support_depth
            ]);

        // 45-ish-degree widening from a one-line breakaway neck
        hull() {
            translate([
                cx - bridge_support_neck / 2,
                wy_bottom - eps,
                support_z0
            ])
                cube([
                    bridge_support_neck,
                    eps,
                    support_depth
                ]);
            translate([
                cx - bridge_support_w / 2,
                y_neck,
                support_z0
            ])
                cube([
                    bridge_support_w,
                    eps,
                    support_depth
                ]);
        }
    }

    // Two rows prevent 97 mm tall, narrow columns wobbling. Each row only
    // bridges between neighboring columns (~22 mm), not across the window.
    for (fraction = [1 / 3, 2 / 3]) {
        tie_y = y_top + fraction * (y_neck - y_top);
        translate([
            first_x - bridge_support_w / 2,
            tie_y - bridge_tie_h / 2,
            support_z0
        ])
            cube([
                last_x - first_x + bridge_support_w,
                bridge_tie_h,
                support_depth
            ]);
    }
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

        shell_lock_slots();
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

    if (window_bridge_supports)
        window_bridge_lattice();

    board_cradle();
}

module board_cradle() {
    // Two straight U-rails point at the open end. The board goes in ZIF-end
    // first; no tilt or sideways move is required. In shell print orientation
    // these constant cross-sections grow vertically and need no supports.
    fp = board_footprint();
    bx = fp[0];
    by = fp[1];
    bw = fp[2];
    bh = fp[3];
    t = 2.0;
    clear = board_pocket_clear;
    capture = board_edge_capture;
    stop_t = 1.6;
    stop_y = by + bh + board_end_clear;
    rail_z0 = z_bay0 - eps;
    groove_z0 = board_z0 - board_z_clear;
    groove_h = board_t + 2 * board_z_clear;
    rail_z1 = groove_z0 + groove_h + 1.0;
    rail_h = rail_z1 - rail_z0;

    // Left rail: groove opens toward +X.
    difference() {
        translate([
            bx - clear - t,
            y_open,
            rail_z0
        ])
            cube([
                t + clear + capture,
                stop_y + stop_t,
                rail_h
            ]);
        translate([
            bx - clear,
            y_open - eps,
            groove_z0
        ])
            cube([
                clear + capture + eps,
                stop_y + eps,
                groove_h
            ]);
    }

    // Right rail: groove opens toward -X.
    difference() {
        translate([
            bx + bw - capture,
            y_open,
            rail_z0
        ])
            cube([
                capture + clear + t,
                stop_y + stop_t,
                rail_h
            ]);
        translate([
            bx + bw - capture - eps,
            y_open - eps,
            groove_z0
        ])
            cube([
                capture + clear + eps,
                stop_y + eps,
                groove_h
            ]);
    }

    // Four low pads set the PCB plane. Their 45° leading ramps prevent the
    // ZIF edge catching while the board slides inward.
    // Keep the first pair beyond fpc_pass_y1; a pad over that backer cutout
    // would be a disconnected island.
    for (yy = [fpc_pass_y1 + 3, stop_y - 9])
        for (xx = [bx + 6, bx + bw - 10])
            union() {
                translate([xx, yy, z_bay0 - eps])
                    cube([4, 4, board_standoff + eps]);
                hull() {
                    translate([xx, yy - 2, z_bay0 - eps])
                        cube([4, eps, eps]);
                    translate([xx, yy, z_bay0 - eps])
                        cube([4, eps, board_standoff + eps]);
                }
            }
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
        union() {
            // Full end plate: flat standing face, except the USB opening.
            translate([0, -cap_t, 0])
                cube([case_w, cap_t, case_depth]);

            // Perimeter lip into the shell rabbet (tight visual seam)
            if (cap_rabbet > 0)
                difference() {
                    translate([0.1, -eps, 0.1])
                        cube([
                            case_w - 0.2,
                            cap_rabbet,
                            case_depth - 0.2
                        ]);
                    translate([
                        cap_rabbet + 0.05,
                        -2 * eps,
                        cap_rabbet + 0.05
                    ])
                        cube([
                            case_w - 2 * cap_rabbet - 0.1,
                            cap_rabbet + 3 * eps,
                            case_depth - 2 * cap_rabbet - 0.1
                        ]);
                }

            // Return skirts hide the seam from front and back.
            if (cap_skirt > 0) {
                translate([0, -eps, -0.02])
                    cube([
                        case_w,
                        cap_skirt,
                        front_lip_t + 0.02
                    ]);
                translate([
                    0,
                    -eps,
                    case_depth - wall - 0.02
                ])
                    cube([
                        case_w,
                        cap_skirt,
                        wall + 0.04
                    ]);
            }

            // Retention tongue butts the panel's FPC edge. Center notch leaves
            // the ribbon route clear.
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

            cap_lock_tongues();
        }

        // USB and the shallow PCB-edge recess are both in the removable cap,
        // so the board follows a straight insertion path in the shell.
        cap_usb_cutouts();
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

    color("#ee6c4d") {
        lock_key_at(-1, explode * 0.2);
        lock_key_at(+1, explode * 0.2);
    }

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
else if (part == "key")
    lock_key_print();
else if (part == "bezel" || part == "tray" || part == "front")
    shell_print(); // legacy aliases
else if (part == "back")
    cap_print();
