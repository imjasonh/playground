// Option A concept — thin display body + centered direct-connect ESP32 backpack
//
// This is intentionally separate from case.scad while the physical layout is
// reviewed. It assumes the raw panel plugs directly into the Waveshare ESP32
// Driver Board, then the board folds flat against the panel back:
//   - ZIF connector at the lower end of the backpack
//   - USB-C at the upper end
//   - board components face outward, away from the glass
//
// Verify the connected board/FPC pose against real hardware before treating
// these placement dimensions as production tolerances.

/* [Parts] */
part = "assembled"; // [assembled, shell, cap, pod_cover, key]
show_components = true;
explode = 0; // [0:1:35]

/* [Panel — Waveshare 7.5 inch raw] */
panel_w = 170.2;
panel_h = 111.2;
panel_t = 1.20;
active_w = 163.2;
active_h = 97.92;
bezel_left = 3.5;
bezel_right = 3.5;
bezel_top = 3.40;

/* [Direct FPC] */
fpc_w = 14.0;
fpc_t = 0.35;
fpc_slot_w = 20.0;
fpc_slot_h = 11.0;
fpc_fold_bay = 8.0;

/* [ESP32 driver board] */
board_w = 29.46;
board_l = 48.25;
board_t = 1.60;
board_comp_h = 8.0;
board_clear = 0.75;
board_standoff = 1.2;
usb_w = 9.2;
usb_h = 3.6;
usb_protrude = 1.5;
usb_clear = 0.7;

/* [Thin display body] */
wall = 2.4;
panel_clear = 0.40;
panel_crush = 0.15;
front_lip_t = 1.4;
backer_t = 2.0;
side_rim = 1.5;
closed_end_wall = 3.0;
cap_t = 2.4;
cap_rabbet = 1.0;
cap_skirt = 2.5;

/* [Centered backpack] */
pod_wall = 2.2;
pod_corner_r = 5.0;
pod_collar_t = 1.2;
pod_collar_h = 2.4;
pod_fit_clear = 0.30;
pod_crush = 0.15;
pod_top_clear = 0.8;
pod_back_t = 2.0;

/* [Rigid cap keys — PLA-safe] */
key_tongue_t = 2.0;
key_reach = 8.0;
key_y = 2.4;
key_z = 1.2;
key_clear = 0.25;
key_wedge = 0.10;
key_head_t = 1.2;
key_head_y = 5.0;
key_head_z = 4.0;
key_tip = 0.8;

/* [FDM] */
elephant_chamfer = 0.3;
window_elephant_chamfer = 0.3;
window_bridge_supports = true;
bridge_support_count = 6;
bridge_support_w = 1.2;
bridge_support_neck = 0.45;
bridge_support_neck_len = 1.2;
bridge_support_gap = 0.20;
bridge_support_setback = 0.25;
bridge_tie_h = 0.8;

/* [Render] */
$fn = 48;
eps = 0.02;

// ---------------------------------------------------------------------------
// Derived geometry — X right, Y up (FPC edge at Y=0), Z toward rear
// ---------------------------------------------------------------------------
bezel_fpc = panel_h - active_h - bezel_top;
slot_t = panel_t + 2 * panel_clear;

z_slot0 = front_lip_t;
z_slot1 = z_slot0 + slot_t;
z_backer0 = z_slot1;
body_depth = z_backer0 + backer_t;

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

// Board is rotated -90°: ZIF at bottom, USB at top.
board_x0 = (case_w - board_w) / 2;
board_y0 = y_panel0;
board_y1 = board_y0 + board_l;
board_z0 = body_depth + board_standoff;

board_free_w = board_w + 2 * board_clear;
board_free_h = board_l + 2 * board_clear;
collar_outer_w = board_free_w + 2 * pod_collar_t;
collar_outer_h = board_free_h + 2 * pod_collar_t;
pod_inner_w = collar_outer_w + 2 * pod_fit_clear;
pod_inner_h = collar_outer_h + 2 * pod_fit_clear;
pod_outer_w = pod_inner_w + 2 * pod_wall;
pod_outer_h = pod_inner_h + 2 * pod_wall;

pod_x0 = (case_w - pod_outer_w) / 2;
pod_y0 =
    board_y0 -
    board_clear -
    pod_collar_t -
    pod_fit_clear -
    pod_wall;
pod_x1 = pod_x0 + pod_outer_w;
pod_y1 = pod_y0 + pod_outer_h;

collar_x0 = (case_w - collar_outer_w) / 2;
collar_y0 = board_y0 - board_clear - pod_collar_t;
collar_inner_x0 = board_x0 - board_clear;
collar_inner_y0 = board_y0 - board_clear;

pod_inner_depth =
    board_standoff +
    board_t +
    board_comp_h +
    pod_top_clear;
pod_back_z = body_depth + pod_inner_depth + pod_back_t;

fpc_slot_x0 = case_w / 2 - fpc_slot_w / 2;
fpc_slot_y0 = board_y0 - 1.0;

key_center_y = 4.6;
key_center_z = z_backer0 + backer_t / 2;
key_body_l = wall + key_clear + key_tongue_t + 0.8;

assert(case_w <= 180,
       "Option A shell must fit the Bambu A1 Mini 180 mm axis");
assert(panel_clear > panel_crush,
       "Panel clearance must exceed crush-rib intrusion");
assert(pod_inner_depth > board_standoff + board_t + board_comp_h,
       "Backpack lacks component clearance");
assert(bridge_support_setback < front_lip_t,
       "Bridge lattice setback exceeds the front lip");

echo("============================================================");
echo("OPTION A — THIN BODY + DIRECT-CONNECT BACKPACK");
echo(str("CLOSED BODY: ", case_w, " x ", case_h + cap_t,
         " x ", body_depth, " mm"));
echo(str("MAX DEPTH AT POD: ", pod_back_z, " mm"));
echo(str("POD FOOTPRINT: ", pod_outer_w, " x ", pod_outer_h, " mm"));
echo(str("POD PROJECTION FROM THIN BACK: ",
         pod_back_z - body_depth, " mm"));
echo(str("BOARD ASSUMPTION: direct FPC, ZIF at Y≈", board_y0,
         ", USB at Y≈", board_y1, " mm"));
echo(str("USB OPENING: ", usb_w + 2 * usb_clear, " x ",
         usb_h + 2 * usb_clear, " mm"));
echo(str("WINDOW SUPPORT: ", bridge_support_count,
         " columns; max bridge≈",
         window_w / (bridge_support_count + 1) - bridge_support_w,
         " mm"));
echo("PARTS: shell + cap + pod_cover + 2× key");
echo("============================================================");

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

module rounded_prism(w, h, r, height) {
    linear_extrude(height = height)
        rounded_rect(w, h, r);
}

module bottom_outer_chamfer_cut(w, h, ch) {
    if (ch > 0)
        difference() {
            translate([-eps, -eps, -eps])
                cube([w + 2 * eps, h + 2 * eps, ch + eps]);
            hull() {
                translate([0, 0, ch])
                    linear_extrude(height = eps)
                        square([w, h]);
                translate([ch, ch, -eps])
                    linear_extrude(height = eps)
                        square([w - 2 * ch, h - 2 * ch]);
            }
        }
}

module at_board() {
    translate([
        board_x0,
        board_y1,
        board_z0
    ])
        rotate([0, 0, -90])
            children();
}

// ---------------------------------------------------------------------------
// Component ghosts
// ---------------------------------------------------------------------------
module panel_ghost() {
    color("Ivory", 0.92)
        translate([
            panel_x0,
            y_panel0,
            z_slot0 + panel_clear
        ])
            cube([panel_w, panel_h, panel_t]);

    color("#4a4a4a", 0.72)
        translate([active_x0, active_y0, -0.02])
            cube([active_w, active_h, 0.04]);

    // Approximate direct FPC bend into the rear ZIF connector.
    color("#c9a227", 0.95) {
        translate([
            case_w / 2 - fpc_w / 2,
            y_panel0 - 2,
            z_slot0 + panel_clear + panel_t / 2 - fpc_t / 2
        ])
            cube([fpc_w, 5, fpc_t]);
        translate([
            case_w / 2 - fpc_w / 2,
            board_y0,
            z_slot1
        ])
            cube([
                fpc_w,
                7,
                board_z0 - z_slot1 + board_t
            ]);
    }
}

module board_ghost() {
    at_board() {
        color("#1b5e20", 0.94)
            cube([board_l, board_w, board_t]);
        color("#111111", 0.94)
            translate([10, (board_w - 16) / 2, board_t])
                cube([22, 16, 3.2]);
        color("#b0b0b0", 0.96)
            translate([
                -usb_protrude,
                (board_w - usb_w) / 2,
                board_t
            ])
                cube([usb_protrude + 2, usb_w, usb_h]);
        color("#222222", 0.94)
            translate([
                board_l - 7,
                (board_w - 16) / 2,
                board_t
            ])
                cube([6, 16, 2.2]);
    }
}

// ---------------------------------------------------------------------------
// Rigid frame-cap keys
// ---------------------------------------------------------------------------
module frame_key() {
    body_end = key_body_l - key_tip;
    seated_y = key_y + 2 * key_clear + key_wedge;
    union() {
        translate([
            -key_head_t,
            -key_head_y / 2,
            -key_head_z / 2
        ])
            cube([
                key_head_t + eps,
                key_head_y,
                key_head_z
            ]);

        hull() {
            translate([0, -seated_y / 2, -key_z / 2])
                cube([eps, seated_y, key_z]);
            translate([
                body_end - eps,
                -key_y / 2,
                -key_z / 2
            ])
                cube([eps, key_y, key_z]);
        }

        hull() {
            translate([
                body_end - eps,
                -key_y / 2,
                -key_z / 2
            ])
                cube([eps, key_y, key_z]);
            translate([
                key_body_l - eps,
                -key_y / 2 + 0.25,
                -key_z / 2 + 0.20
            ])
                cube([
                    eps,
                    key_y - 0.5,
                    key_z - 0.4
                ]);
        }
    }
}

module frame_key_at(side, pull = 0) {
    if (side < 0)
        translate([-pull, key_center_y, key_center_z])
            frame_key();
    else
        translate([
            case_w + pull,
            key_center_y,
            key_center_z
        ])
            mirror([1, 0, 0])
                frame_key();
}

module frame_key_print() {
    translate([
        key_head_z / 2,
        key_head_y / 2,
        key_head_t
    ])
        rotate([0, -90, 0])
            frame_key();
}

module shell_key_slots() {
    hole_y = key_y + 2 * key_clear;
    hole_z = key_z + 2 * key_clear;
    for (x = [-eps, case_w - wall - eps])
        translate([
            x,
            key_center_y - hole_y / 2,
            key_center_z - hole_z / 2
        ])
            cube([wall + 2 * eps, hole_y, hole_z]);
}

module cap_key_tongues() {
    tongue_z0 =
        key_center_z - key_z / 2 - key_clear - 0.3;
    tongue_h = key_z + 2 * key_clear + 0.6;
    difference() {
        union() {
            translate([
                wall + key_clear,
                -eps,
                tongue_z0
            ])
                cube([key_tongue_t, key_reach + eps, tongue_h]);
            translate([
                case_w - wall - key_clear - key_tongue_t,
                -eps,
                tongue_z0
            ])
                cube([key_tongue_t, key_reach + eps, tongue_h]);
        }
        translate([
            -eps,
            key_center_y - key_y / 2 - key_clear,
            key_center_z - key_z / 2 - key_clear
        ])
            cube([
                case_w + 2 * eps,
                key_y + 2 * key_clear,
                key_z + 2 * key_clear
            ]);
    }
}

// ---------------------------------------------------------------------------
// Sacrificial window-lintel lattice
// ---------------------------------------------------------------------------
module window_bridge_lattice() {
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
// Backpack landing collar + board support
// ---------------------------------------------------------------------------
module pod_collar_and_cradle() {
    // Rounded collar receives the separate pod cover.
    difference() {
        translate([collar_x0, collar_y0, body_depth - eps])
            rounded_prism(
                collar_outer_w,
                collar_outer_h,
                max(1, pod_corner_r - pod_wall - pod_fit_clear),
                pod_collar_h + eps
            );
        translate([
            collar_inner_x0,
            collar_inner_y0,
            body_depth - 2 * eps
        ])
            rounded_prism(
                board_free_w,
                board_free_h,
                max(0.6,
                    pod_corner_r -
                    pod_wall -
                    pod_fit_clear -
                    pod_collar_t),
                pod_collar_h + 3 * eps
            );

        // Direct-FPC entry through the lower collar wall.
        translate([
            case_w / 2 - fpc_slot_w / 2,
            collar_y0 - eps,
            body_depth - 2 * eps
        ])
            cube([
                fpc_slot_w,
                pod_collar_t + 2 * eps,
                pod_collar_h + 4 * eps
            ]);
    }

    // Sparse outer ribs make the small cover friction fit tunable in PLA.
    rib_len = 8;
    for (yy = [
        collar_y0 + collar_outer_h * 0.28,
        collar_y0 + collar_outer_h * 0.72 - rib_len
    ]) {
        translate([
            collar_x0 - pod_crush,
            yy,
            body_depth
        ])
            cube([
                pod_crush + eps,
                rib_len,
                pod_collar_h
            ]);
        translate([
            collar_x0 + collar_outer_w - eps,
            yy,
            body_depth
        ])
            cube([
                pod_crush + eps,
                rib_len,
                pod_collar_h
            ]);
    }

    // Four standoff pads; board components face away from the glass.
    for (xx = [board_x0 + 5, board_x0 + board_w - 9])
        for (yy = [
            fpc_slot_y0 + fpc_slot_h + 2,
            board_y1 - 11
        ])
            translate([xx, yy, body_depth - eps])
                cube([4, 4, board_standoff + eps]);
}

// ---------------------------------------------------------------------------
// Thin display shell
// ---------------------------------------------------------------------------
module shell(include_window_supports = window_bridge_supports) {
    difference() {
        cube([case_w, case_h, body_depth]);

        // Active-area window
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
                translate([
                    window_x0,
                    window_y0,
                    window_elephant_chamfer
                ])
                    cube([window_w, window_h, eps]);
            }

        // End-loaded panel slot
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

        // FPC folds directly through the backer into the board ZIF.
        translate([
            fpc_slot_x0,
            fpc_slot_y0,
            z_slot1 - eps
        ])
            cube([
                fpc_slot_w,
                fpc_slot_h,
                backer_t + 2 * eps
            ]);

        // Cap rabbet
        if (cap_rabbet > 0)
            difference() {
                translate([-eps, -eps, -eps])
                    cube([
                        case_w + 2 * eps,
                        cap_rabbet + eps,
                        body_depth + 2 * eps
                    ]);
                translate([
                    cap_rabbet,
                    -2 * eps,
                    cap_rabbet
                ])
                    cube([
                        case_w - 2 * cap_rabbet,
                        cap_rabbet + 3 * eps,
                        body_depth - 2 * cap_rabbet
                    ]);
            }

        shell_key_slots();
    }

    if (panel_crush > 0) {
        rib_len = 14;
        rib_z = z_slot0 + panel_clear;
        rib_h = panel_t * 0.85;
        for (yy = [
            y_panel0 + 18,
            y_panel0 + panel_h - 18 - rib_len
        ]) {
            translate([
                panel_x0 - panel_clear - 0.15,
                yy,
                rib_z
            ])
                cube([
                    panel_crush + 0.15,
                    rib_len,
                    rib_h
                ]);
            translate([
                panel_x0 + panel_w + panel_clear - panel_crush,
                yy,
                rib_z
            ])
                cube([
                    panel_crush + 0.15,
                    rib_len,
                    rib_h
                ]);
        }
    }

    if (include_window_supports)
        window_bridge_lattice();

    pod_collar_and_cradle();
}

module shell_print() {
    translate([0, 0, case_h])
        rotate([-90, 0, 0])
            difference() {
                shell();
                if (elephant_chamfer > 0)
                    translate([0, case_h + eps, 0])
                        rotate([90, 0, 0])
                            bottom_outer_chamfer_cut(
                                case_w,
                                body_depth + pod_collar_h,
                                elephant_chamfer
                            );
            }
}

// ---------------------------------------------------------------------------
// Thin edge cap
// ---------------------------------------------------------------------------
module cap() {
    union() {
        translate([0, -cap_t, 0])
            cube([case_w, cap_t, body_depth]);

        if (cap_rabbet > 0)
            difference() {
                translate([0.1, -eps, 0.1])
                    cube([
                        case_w - 0.2,
                        cap_rabbet,
                        body_depth - 0.2
                    ]);
                translate([
                    cap_rabbet + 0.05,
                    -2 * eps,
                    cap_rabbet + 0.05
                ])
                    cube([
                        case_w - 2 * cap_rabbet - 0.1,
                        cap_rabbet + 3 * eps,
                        body_depth - 2 * cap_rabbet - 0.1
                    ]);
            }

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
                body_depth - backer_t - 0.02
            ])
                cube([
                    case_w,
                    cap_skirt,
                    backer_t + 0.04
                ]);
        }

        // Panel stop, notched for direct FPC.
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
                case_w / 2 - fpc_slot_w / 2,
                -2 * eps,
                z_slot0 - eps
            ])
                cube([
                    fpc_slot_w,
                    tongue_len + 3 * eps,
                    slot_t + 2 * eps
                ]);
        }

        cap_key_tongues();
    }
}

module cap_print() {
    translate([0, body_depth, 0])
        rotate([90, 0, 0])
            translate([0, cap_t, 0])
                difference() {
                    cap();
                    if (elephant_chamfer > 0)
                        translate([0, -cap_t - eps, 0])
                            rotate([-90, 0, 0])
                                bottom_outer_chamfer_cut(
                                    case_w,
                                    body_depth,
                                    elephant_chamfer
                                );
                }
}

// ---------------------------------------------------------------------------
// Separate rounded backpack cover — outer rear face prints on bed
// ---------------------------------------------------------------------------
module pod_usb_cutout() {
    cw = usb_w + 2 * usb_clear;
    ch = usb_h + 2 * usb_clear;
    at_board()
        translate([
            -usb_protrude - pod_wall - 3,
            (board_w - cw) / 2,
            board_t - usb_clear
        ])
            cube([
                usb_protrude + 2 * pod_wall + 7,
                cw,
                ch
            ]);
}

module pod_cover() {
    difference() {
        translate([pod_x0, pod_y0, body_depth])
            rounded_prism(
                pod_outer_w,
                pod_outer_h,
                pod_corner_r,
                pod_back_z - body_depth
            );

        // Open front cavity; rear plate remains pod_back_t thick.
        translate([
            pod_x0 + pod_wall,
            pod_y0 + pod_wall,
            body_depth - eps
        ])
            rounded_prism(
                pod_inner_w,
                pod_inner_h,
                max(1, pod_corner_r - pod_wall),
                pod_back_z -
                pod_back_t -
                body_depth +
                2 * eps
            );

        pod_usb_cutout();

        // Fingernail/pry relief at lower edge.
        translate([
            case_w / 2 - 5,
            pod_y0 - eps,
            body_depth - eps
        ])
            cube([
                10,
                pod_wall + 2 * eps,
                1.2
            ]);
    }
}

module pod_cover_print() {
    // Reflect rear face to Z=0; walls grow upward without support.
    translate([0, 0, pod_back_z])
        mirror([0, 0, 1])
            pod_cover();
}

// ---------------------------------------------------------------------------
// Assembly
// ---------------------------------------------------------------------------
module assembled() {
    color("#3d5a80")
        shell(false); // show the finished shape after lattice removal

    translate([0, -explode, 0])
        color("#293241")
            cap();

    translate([0, 0, explode])
        color("#23344d")
            pod_cover();

    color("#ee6c4d") {
        frame_key_at(-1, explode * 0.2);
        frame_key_at(+1, explode * 0.2);
    }

    if (show_components) {
        panel_ghost();
        translate([0, 0, explode * 0.4])
            board_ghost();
    }
}

if (part == "assembled")
    assembled();
else if (part == "shell")
    shell_print();
else if (part == "cap")
    cap_print();
else if (part == "pod_cover")
    pod_cover_print();
else if (part == "key")
    frame_key_print();
