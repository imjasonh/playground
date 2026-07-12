## Yard Crane — main game controller.
## Builds the circular yard, drives scoring, and wires the crane + HUD.
extends Node3D

const PLATFORM_COUNT := 8
const YARD_RADIUS := 18.0
const ROUND_SECONDS := 180.0

@onready var crane: Crane = $Crane
@onready var yard: Node3D = $Yard
@onready var payloads_root: Node3D = $Payloads
@onready var hud: CanvasLayer = $HUD
@onready var camera: Camera3D = $CameraRig/Camera3D

var score: int = 0
var delivered: int = 0
var time_left: float = ROUND_SECONDS
var game_over: bool = false
var _spawn_queue: Array[Dictionary] = []
var _rng := RandomNumberGenerator.new()

signal score_changed(score: int)
signal time_changed(seconds: float)
signal status_changed(text: String)
signal game_ended(final_score: int, delivered: int)


func _ready() -> void:
	_rng.randomize()
	_build_environment()
	_build_yard()
	_seed_payloads()
	crane.payload_delivered.connect(_on_payload_delivered)
	crane.grab_changed.connect(_on_grab_changed)
	crane.rough_landing.connect(_on_rough_landing)
	score_changed.emit(score)
	time_changed.emit(time_left)
	status_changed.emit("Lift crates onto matching pads. Go gentle — slamming costs points.")


func _process(delta: float) -> void:
	if game_over:
		return
	time_left = maxf(0.0, time_left - delta)
	time_changed.emit(time_left)
	if time_left <= 0.0:
		_end_game()


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

	# Ground disc
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

	# Center ring marking
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
	# Platforms around the circle at mixed heights: pickups and drop-offs.
	# Even indices = pickup pads, odd = drop-off pads (color-matched pairs).
	var heights := [1.2, 3.5, 2.0, 5.0, 1.5, 4.2, 2.8, 6.0]
	var colors := [
		Color(0.85, 0.35, 0.2),
		Color(0.2, 0.55, 0.75),
		Color(0.3, 0.7, 0.35),
		Color(0.75, 0.55, 0.15),
	]
	for i in PLATFORM_COUNT:
		var angle := TAU * float(i) / float(PLATFORM_COUNT)
		var pos := Vector3(cos(angle) * YARD_RADIUS, 0.0, sin(angle) * YARD_RADIUS)
		var height: float = heights[i]
		var color_idx := i / 2
		var color: Color = colors[color_idx % colors.size()]
		var is_drop := (i % 2) == 1
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
	body.collision_layer = 8  # platforms
	body.collision_mask = 0
	body.position = pos
	body.set_meta("is_drop", is_drop)
	body.set_meta("color_idx", color_idx)
	body.set_meta("pad_height", height)

	# Support column
	var column := MeshInstance3D.new()
	var col_mesh := BoxMesh.new()
	col_mesh.size = Vector3(1.4, height, 1.4)
	column.mesh = col_mesh
	column.position.y = height * 0.5
	var col_mat := StandardMaterial3D.new()
	col_mat.albedo_color = Color(0.35, 0.38, 0.4)
	column.material_override = col_mat
	body.add_child(column)

	# Deck
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

	# Rim marker — brighter for drop pads
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

	# Invisible delivery trigger volume above drop pads
	if is_drop:
		var area := Area3D.new()
		area.name = "DropZone"
		area.collision_layer = 0
		area.collision_mask = 2  # payloads
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
	# Place a crate on each pickup pad.
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


func _on_payload_delivered(payload: Payload, soft: bool) -> void:
	if game_over:
		return
	var color_idx := payload.color_idx
	var base := 100
	var mass_bonus := int(payload.mass_kg / 10.0)
	var soft_bonus := 50 if soft else 0
	var time_bonus := int(clampf(time_left / ROUND_SECONDS, 0.0, 1.0) * 40.0)
	var gained := base + mass_bonus + soft_bonus + time_bonus
	score += gained
	delivered += 1
	score_changed.emit(score)
	var feel := "Soft set" if soft else "Delivered"
	status_changed.emit("%s +%d  ·  %d loads" % [feel, gained, delivered])
	payload.queue_free()
	# Respawn a new crate on the matching pickup pad after a beat.
	await get_tree().create_timer(1.2).timeout
	if game_over:
		return
	for entry in _spawn_queue:
		if not entry["is_drop"] and entry["color_idx"] == color_idx:
			_spawn_payload_on_pad(entry)
			break


func _on_grab_changed(holding: bool) -> void:
	if holding:
		status_changed.emit("Hooked. Ease it over — watch the swing.")
	else:
		status_changed.emit("Hook free.")


func _on_rough_landing(penalty: int) -> void:
	score = maxi(0, score - penalty)
	score_changed.emit(score)
	status_changed.emit("Hard contact −%d" % penalty)


func _end_game() -> void:
	game_over = true
	crane.set_enabled(false)
	status_changed.emit("Shift over — Space to run another.")
	game_ended.emit(score, delivered)


func _restart() -> void:
	get_tree().reload_current_scene()
