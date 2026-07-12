## Tower crane with slow, heavy controls and a swinging hook.
class_name Crane
extends Node3D

signal payload_delivered(payload: Payload, soft: bool)
signal grab_changed(holding: bool)
signal rough_landing(penalty: int)

# Motion limits — deliberately slow for a big crane feel.
const ROTATE_ACCEL := 0.18
const ROTATE_MAX := 0.35
const ROTATE_DRAG := 0.55
const TROLLEY_ACCEL := 2.2
const TROLLEY_MAX := 3.0
const TROLLEY_MIN_R := 4.0
const TROLLEY_MAX_R := 20.0
const HOOK_ACCEL := 2.0
const HOOK_MAX := 2.6
const CABLE_MIN := 2.0
const CABLE_MAX := 14.0
const GRAB_DISTANCE := 1.35
const SWING_DAMP := 0.35
const GRAVITY := 9.8

@onready var pivot: Node3D = $Pivot
@onready var boom: Node3D = $Pivot/Boom
@onready var trolley: Node3D = $Pivot/Boom/Trolley
@onready var hook: Node3D = $Pivot/Boom/Trolley/Hook
@onready var cable_mesh: MeshInstance3D = $Pivot/Boom/Trolley/Cable
@onready var hook_body: RigidBody3D = $Pivot/Boom/Trolley/Hook/HookBody
@onready var magnet: Area3D = $Pivot/Boom/Trolley/Hook/HookBody/Magnet

var enabled: bool = true
var _yaw: float = 0.0
var _yaw_vel: float = 0.0
var _trolley_r: float = 10.0
var _trolley_vel: float = 0.0
var _cable_len: float = 6.0
var _cable_vel: float = 0.0

# Hook swing state in trolley-local space (x along boom, z lateral).
var _swing := Vector2.ZERO
var _swing_vel := Vector2.ZERO

var _held: Payload = null
var _held_joint: Generic6DOFJoint3D = null
var _input_rotate: float = 0.0
var _input_trolley: float = 0.0
var _input_hook: float = 0.0
var _grab_pressed: bool = false

# External touch HUD can drive these.
var touch_rotate: float = 0.0
var touch_trolley: float = 0.0
var touch_hook: float = 0.0


func _ready() -> void:
	_build_visuals_if_needed()
	hook_body.freeze = true
	magnet.body_entered.connect(_on_magnet_body)
	# Detect deliveries via drop zones
	get_tree().node_added.connect(_on_node_added)
	_connect_existing_drop_zones()


func set_enabled(value: bool) -> void:
	enabled = value


func set_touch_axis(rotate: float, trolley_axis: float, hook_axis: float) -> void:
	touch_rotate = clampf(rotate, -1.0, 1.0)
	touch_trolley = clampf(trolley_axis, -1.0, 1.0)
	touch_hook = clampf(hook_axis, -1.0, 1.0)


func request_grab_toggle() -> void:
	_grab_pressed = true


func _physics_process(delta: float) -> void:
	_read_input()
	if not enabled:
		_input_rotate = 0.0
		_input_trolley = 0.0
		_input_hook = 0.0

	# --- Slewing (rotation) ---
	_yaw_vel += _input_rotate * ROTATE_ACCEL * delta
	_yaw_vel = clampf(_yaw_vel, -ROTATE_MAX, ROTATE_MAX)
	if is_zero_approx(_input_rotate):
		_yaw_vel = move_toward(_yaw_vel, 0.0, ROTATE_DRAG * delta)
	_yaw += _yaw_vel * delta
	pivot.rotation.y = _yaw

	# --- Trolley travel ---
	_trolley_vel += _input_trolley * TROLLEY_ACCEL * delta
	_trolley_vel = clampf(_trolley_vel, -TROLLEY_MAX, TROLLEY_MAX)
	if is_zero_approx(_input_trolley):
		_trolley_vel = move_toward(_trolley_vel, 0.0, TROLLEY_ACCEL * 1.4 * delta)
	_trolley_r = clampf(_trolley_r + _trolley_vel * delta, TROLLEY_MIN_R, TROLLEY_MAX_R)
	trolley.position.x = _trolley_r

	# --- Hoist ---
	_cable_vel += _input_hook * HOOK_ACCEL * delta
	_cable_vel = clampf(_cable_vel, -HOOK_MAX, HOOK_MAX)
	if is_zero_approx(_input_hook):
		_cable_vel = move_toward(_cable_vel, 0.0, HOOK_ACCEL * 1.6 * delta)
	_cable_len = clampf(_cable_len + _cable_vel * delta, CABLE_MIN, CABLE_MAX)

	# Pendulum driven by support-point motion (trolley + slew).
	var drive := Vector2(_trolley_vel * 0.22, _yaw_vel * _trolley_r * 0.65)
	_swing_vel += drive * delta
	var omega2 := GRAVITY / maxf(_cable_len, 0.5)
	_swing_vel += -_swing * omega2 * delta
	_swing_vel *= (1.0 - SWING_DAMP * delta)
	_swing += _swing_vel * delta
	var max_swing := minf(2.8, _cable_len * 0.45)
	if _swing.length() > max_swing:
		_swing = _swing.normalized() * max_swing
		_swing_vel *= 0.5

	# Heavier load = bigger swing response and slower settle.
	var load_factor := 1.0
	if _held:
		load_factor = 1.0 + (_held.mass_kg / 380.0)
		_swing_vel *= (1.0 - 0.05 * delta)

	hook.position = Vector3(_swing.x * load_factor, -_cable_len, _swing.y * load_factor)
	_update_cable_visual()

	if _grab_pressed:
		_grab_pressed = false
		_toggle_grab()

	_check_held_delivery()


func _read_input() -> void:
	_input_rotate = Input.get_axis("rotate_left", "rotate_right")
	_input_trolley = Input.get_axis("boom_in", "boom_out")
	# hook_up raises (shortens cable) => negative length change
	_input_hook = Input.get_axis("hook_up", "hook_down")
	if not is_zero_approx(touch_rotate) or not is_zero_approx(touch_trolley) or not is_zero_approx(touch_hook):
		_input_rotate = touch_rotate
		_input_trolley = touch_trolley
		_input_hook = touch_hook
	if Input.is_action_just_pressed("grab"):
		_grab_pressed = true


func _update_cable_visual() -> void:
	if not is_instance_valid(cable_mesh):
		return
	var end := hook.position
	var dist := end.length()
	if dist < 0.05:
		cable_mesh.visible = false
		return
	cable_mesh.visible = true
	cable_mesh.position = end * 0.5
	cable_mesh.scale = Vector3(1.0, dist, 1.0)
	# Orient cylinder (Y-up mesh) along trolley → hook
	var up := end.normalized()
	var axis := Vector3.UP.cross(up)
	var angle := Vector3.UP.angle_to(up)
	if axis.length() > 0.001:
		cable_mesh.basis = Basis(axis.normalized(), angle)
	else:
		cable_mesh.basis = Basis.IDENTITY if up.y > 0.0 else Basis(Vector3.RIGHT, PI)
	cable_mesh.scale = Vector3(1.0, dist, 1.0)


func _toggle_grab() -> void:
	if _held:
		_release()
	else:
		_try_grab()


func _try_grab() -> void:
	var candidates: Array[Payload] = []
	for body in magnet.get_overlapping_bodies():
		if body is Payload:
			candidates.append(body)
	# Also proximity search — magnet area may miss thin timing
	for node in get_tree().get_nodes_in_group("payloads"):
		if node is Payload and not node.is_held:
			var p := node as Payload
			if p.global_position.distance_to(hook_body.global_position) <= GRAB_DISTANCE:
				if p not in candidates:
					candidates.append(p)
	if candidates.is_empty():
		return
	candidates.sort_custom(func(a: Payload, b: Payload) -> bool:
		return a.global_position.distance_to(hook_body.global_position) < b.global_position.distance_to(hook_body.global_position)
	)
	_attach(candidates[0])


func _attach(payload: Payload) -> void:
	_held = payload
	payload.pick_up(hook_body)
	# Parent-follow: kinematic attach for predictable crane game feel
	grab_changed.emit(true)


func _release() -> void:
	if _held == null:
		return
	var payload := _held
	var impact_speed := _swing_vel.length() + absf(_cable_vel) + absf(_trolley_vel) * 0.3 + absf(_yaw_vel) * _trolley_r * 0.3
	_held = null
	payload.drop(hook_body.global_position, _estimate_release_velocity())
	grab_changed.emit(false)
	# Rough release mid-air isn't a landing; landing checked on delivery / floor later
	if impact_speed > 3.5:
		var penalty := int(clampf(impact_speed * 8.0, 10.0, 60.0))
		rough_landing.emit(penalty)


func _estimate_release_velocity() -> Vector3:
	# World-space velocity of hook tip from crane motion + swing.
	var tangential := pivot.global_transform.basis * Vector3(0.0, 0.0, _yaw_vel * _trolley_r)
	var radial := pivot.global_transform.basis * Vector3(_trolley_vel, 0.0, 0.0)
	var hoist := Vector3(0.0, -_cable_vel, 0.0)
	var swing_world := pivot.global_transform.basis * Vector3(_swing_vel.x, 0.0, _swing_vel.y)
	return tangential + radial + hoist + swing_world


func _check_held_delivery() -> void:
	# Soft delivery while still hooked: lower onto matching pad and release nearby.
	pass


func _on_magnet_body(_body: Node) -> void:
	pass


func _connect_existing_drop_zones() -> void:
	for area in _find_drop_zones(get_tree().root):
		_wire_drop_zone(area)


func _on_node_added(node: Node) -> void:
	if node is Area3D and node.name == "DropZone":
		_wire_drop_zone(node)


func _find_drop_zones(node: Node) -> Array[Area3D]:
	var out: Array[Area3D] = []
	if node is Area3D and node.name == "DropZone":
		out.append(node)
	for child in node.get_children():
		out.append_array(_find_drop_zones(child))
	return out


func _wire_drop_zone(area: Area3D) -> void:
	if area.has_meta("_wired"):
		return
	area.set_meta("_wired", true)
	area.body_entered.connect(func(body: Node) -> void:
		_on_drop_zone_body(area, body)
	)


func _on_drop_zone_body(area: Area3D, body: Node) -> void:
	if body is Payload:
		var payload := body as Payload
		if payload.is_held:
			return
		if payload.color_idx != int(area.get_meta("color_idx")):
			return
		# Already delivered?
		if payload.has_meta("delivered"):
			return
		payload.set_meta("delivered", true)
		var speed := payload.linear_velocity.length()
		var soft := speed < 2.2
		if not soft:
			var penalty := int(clampf(speed * 10.0, 15.0, 80.0))
			rough_landing.emit(penalty)
		payload_delivered.emit(payload, soft)


func _build_visuals_if_needed() -> void:
	# Scene provides structure; ensure cable material exists.
	if cable_mesh.mesh == null:
		var cyl := CylinderMesh.new()
		cyl.top_radius = 0.04
		cyl.bottom_radius = 0.04
		cyl.height = 1.0
		cable_mesh.mesh = cyl
	if cable_mesh.material_override == null:
		var mat := StandardMaterial3D.new()
		mat.albedo_color = Color(0.75, 0.78, 0.8)
		cable_mesh.material_override = mat
