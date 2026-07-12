## Yard Crane — main game controller.
## Three crates, three destinations; stopwatch until the yard is clear.
extends Node3D

const SLOT_COUNT := 6
const CRATE_COUNT := 3
const YARD_RADIUS := 18.0

## Coral, steel blue, amber — no green.
const PAD_COLORS := [
	Color(0.85, 0.35, 0.2),
	Color(0.2, 0.55, 0.75),
	Color(0.85, 0.62, 0.18),
]

@onready var crane: Crane = $Crane
@onready var yard: Node3D = $Yard
@onready var payloads_root: Node3D = $Payloads
@onready var hud: CanvasLayer = $HUD
@onready var camera: Camera3D = $CameraRig/Camera3D

var delivered: int = 0
var elapsed: float = 0.0
var game_over: bool = false
var _spawn_queue: Array[Dictionary] = []
var _rng := RandomNumberGenerator.new()

signal progress_changed(delivered: int, total: int)
signal time_changed(seconds: float)
signal status_changed(text: String)
signal game_ended(elapsed_seconds: float, soft_count: int)


func _ready() -> void:
	_rng.randomize()
	_build_environment()
	_build_yard()
	_seed_payloads()
	crane.payload_delivered.connect(_on_payload_delivered)
	crane.grab_changed.connect(_on_grab_changed)
	crane.rough_landing.connect(_on_rough_landing)
	progress_changed.emit(delivered, CRATE_COUNT)
	time_changed.emit(elapsed)
	status_changed.emit("Move all three crates to their matching pads. Clock is running.")


func _process(delta: float) -> void:
	if game_over:
		return
	elapsed += delta
	time_changed.emit(elapsed)


func _unhandled_input(event: InputEvent) -> void:
	if game_over and event.is_action_pressed("grab"):
		_restart()
		get_viewport().set_input_as_handled()


func _build_environment() -> void:
	var world_env := WorldEnvironment.new()
	var env := Environment.new()
	env.background_mode = Environment.BG_COLOR
	env.background_color = Color(0.55, 0.68, 0.78)
	env.ambient_light_source = Environment.AMBIENT_SOURCE_COLOR
	env.ambient_light_color = Color(0.72, 0.78, 0.86)
	env.ambient_light_energy = 0.85
	env.tonemap_mode = Environment.TONE_MAPPER_FILMIC
	env.glow_enabled = false
	world_env.environment = env
	add_child(world_env)

	var sun := DirectionalLight3D.new()
	sun.rotation_degrees = Vector3(-48, 35, 0)
	sun.light_energy = 1.15
	sun.shadow_enabled = true
	add_child(sun)

	var ground := StaticBody3D.new()
	ground.collision_layer = 1
	ground.collision_mask = 0
	var mesh := MeshInstance3D.new()
	var cyl := CylinderMesh.new()
	cyl.top_radius = YARD_RADIUS + 6.0
	cyl.bottom_radius = YARD_RADIUS + 6.0
	cyl.height = 0.4
	mesh.mesh = cyl
	var mat := StandardMaterial3D.new()
	mat.albedo_color = Color(0.42, 0.45, 0.4)
	mat.roughness = 0.95
	mesh.material_override = mat
	ground.add_child(mesh)
	var col := CollisionShape3D.new()
	var shape := CylinderShape3D.new()
	shape.radius = YARD_RADIUS + 6.0
	shape.height = 0.4
	col.shape = shape
	ground.add_child(col)
	ground.position.y = -0.2
	yard.add_child(ground)

	var ring := MeshInstance3D.new()
	var torus := TorusMesh.new()
	torus.inner_radius = 2.2
	torus.outer_radius = 2.6
	ring.mesh = torus
	var ring_mat := StandardMaterial3D.new()
	ring_mat.albedo_color = Color(0.85, 0.7, 0.2)
	ring.material_override = ring_mat
	ring.position.y = 0.05
	yard.add_child(ring)


func _build_yard() -> void:
	# Six pads around the circle. Each color's pickup and drop sit opposite
	# each other (3 slots apart), never adjacent.
	var heights := [1.4, 3.8, 2.2, 5.2, 1.8, 4.6]
	# Slot i: pickup for color i at even phase, drop for color i opposite.
	# color 0: pickup slot 0 → drop slot 3
	# color 1: pickup slot 2 → drop slot 5
	# color 2: pickup slot 4 → drop slot 1
	var layout := [
		{"slot": 0, "color_idx": 0, "is_drop": false},
		{"slot": 1, "color_idx": 2, "is_drop": true},
		{"slot": 2, "color_idx": 1, "is_drop": false},
		{"slot": 3, "color_idx": 0, "is_drop": true},
		{"slot": 4, "color_idx": 2, "is_drop": false},
		{"slot": 5, "color_idx": 1, "is_drop": true},
	]
	# Shuffle color→pair mapping a bit by rotating which opposite pair is which,
	# while keeping every pickup/drop pair 180° apart.
	var rotation := _rng.randi_range(0, SLOT_COUNT - 1)
	if rotation % 2 == 1:
		# Keep even offset so opposites stay opposite under a slot rotate.
		rotation -= 1

	for entry in layout:
		var slot: int = (int(entry["slot"]) + rotation) % SLOT_COUNT
		var angle := TAU * float(slot) / float(SLOT_COUNT)
		var pos := Vector3(cos(angle) * YARD_RADIUS, 0.0, sin(angle) * YARD_RADIUS)
		var height: float = heights[slot]
		var color_idx: int = entry["color_idx"]
		var is_drop: bool = entry["is_drop"]
		var color: Color = PAD_COLORS[color_idx]
		var platform := _make_platform(pos, height, color, is_drop, color_idx)
		yard.add_child(platform)
		_spawn_queue.append({
			"pad": platform,
			"color_idx": color_idx,
			"is_drop": is_drop,
			"height": height,
			"angle": angle,
		})


func _make_platform(pos: Vector3, height: float, color: Color, is_drop: bool, color_idx: int) -> StaticBody3D:
	var body := StaticBody3D.new()
	body.collision_layer = 8
	body.collision_mask = 0
	body.position = pos
	body.set_meta("is_drop", is_drop)
	body.set_meta("color_idx", color_idx)
	body.set_meta("pad_height", height)

	var column := MeshInstance3D.new()
	var col_mesh := BoxMesh.new()
	col_mesh.size = Vector3(1.4, height, 1.4)
	column.mesh = col_mesh
	column.position.y = height * 0.5
	var col_mat := StandardMaterial3D.new()
	col_mat.albedo_color = Color(0.35, 0.38, 0.4)
	column.material_override = col_mat
	body.add_child(column)

	var deck := MeshInstance3D.new()
	var deck_mesh := BoxMesh.new()
	deck_mesh.size = Vector3(3.6, 0.35, 3.6)
	deck.mesh = deck_mesh
	deck.position.y = height + 0.175
	var deck_mat := StandardMaterial3D.new()
	deck_mat.albedo_color = color.darkened(0.15) if is_drop else color.lightened(0.1)
	deck_mat.roughness = 0.7
	deck.material_override = deck_mat
	body.add_child(deck)

	var rim := MeshInstance3D.new()
	var rim_mesh := TorusMesh.new()
	rim_mesh.inner_radius = 1.35
	rim_mesh.outer_radius = 1.55
	rim.mesh = rim_mesh
	rim.position.y = height + 0.4
	var rim_mat := StandardMaterial3D.new()
	rim_mat.albedo_color = color
	rim_mat.emission_enabled = is_drop
	rim_mat.emission = color
	rim_mat.emission_energy_multiplier = 0.55 if is_drop else 0.0
	rim.material_override = rim_mat
	body.add_child(rim)

	var shape := CollisionShape3D.new()
	var box := BoxShape3D.new()
	box.size = Vector3(3.6, height + 0.35, 3.6)
	shape.shape = box
	shape.position.y = (height + 0.35) * 0.5
	body.add_child(shape)

	if is_drop:
		var area := Area3D.new()
		area.name = "DropZone"
		area.collision_layer = 0
		area.collision_mask = 2
		area.monitoring = true
		area.position.y = height + 1.2
		var area_shape := CollisionShape3D.new()
		var area_box := BoxShape3D.new()
		area_box.size = Vector3(3.2, 2.0, 3.2)
		area_shape.shape = area_box
		area.add_child(area_shape)
		area.set_meta("color_idx", color_idx)
		area.set_meta("pad_height", height)
		body.add_child(area)

	return body


func _seed_payloads() -> void:
	for entry in _spawn_queue:
		if entry["is_drop"]:
			continue
		_spawn_payload_on_pad(entry)


func _spawn_payload_on_pad(entry: Dictionary) -> void:
	var pad: Node3D = entry["pad"]
	var color_idx: int = entry["color_idx"]
	var height: float = entry["height"]
	var payload := Payload.create(color_idx, _rng.randf_range(180.0, 420.0))
	payloads_root.add_child(payload)
	payload.global_position = pad.global_position + Vector3(0.0, height + 1.1, 0.0)
	payload.freeze = false


var _soft_count: int = 0


func _on_payload_delivered(payload: Payload, soft: bool) -> void:
	if game_over:
		return
	if soft:
		_soft_count += 1
	delivered += 1
	progress_changed.emit(delivered, CRATE_COUNT)
	var feel := "Soft set" if soft else "Set down"
	status_changed.emit("%s · %d / %d crates" % [feel, delivered, CRATE_COUNT])
	# Leave the crate on the pad so the yard fills as you finish.
	payload.settle_on_pad()
	if delivered >= CRATE_COUNT:
		_end_game()


func _on_grab_changed(holding: bool) -> void:
	if holding:
		status_changed.emit("Hooked. Ease it over — watch the swing.")
	elif not game_over:
		status_changed.emit("Hook free.")


func _on_rough_landing(_penalty: int) -> void:
	if game_over:
		return
	status_changed.emit("Hard contact — ease off the swing.")


func _end_game() -> void:
	game_over = true
	crane.set_enabled(false)
	status_changed.emit("Yard clear — Space to run another.")
	game_ended.emit(elapsed, _soft_count)


func _restart() -> void:
	get_tree().reload_current_scene()
