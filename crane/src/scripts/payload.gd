## Color-coded crate with mass that affects crane swing feel.
class_name Payload
extends RigidBody3D

const COLORS := [
	Color(0.85, 0.35, 0.2),
	Color(0.2, 0.55, 0.75),
	Color(0.85, 0.62, 0.18),
]

var color_idx: int = 0
var mass_kg: float = 250.0
var is_held: bool = false
var _anchor: Node3D = null
var _follow_offset := Vector3(0.0, -0.85, 0.0)


static func create(p_color_idx: int, p_mass: float) -> Payload:
	var p := Payload.new()
	p.color_idx = p_color_idx
	p.mass_kg = p_mass
	p._build()
	return p


func _build() -> void:
	collision_layer = 2
	collision_mask = 1 | 8  # world + platforms
	mass = mass_kg / 50.0  # scale for engine stability
	continuous_cd = true
	linear_damp = 0.4
	angular_damp = 0.8
	can_sleep = true
	add_to_group("payloads")

	var size := Vector3(1.1, 1.1, 1.1)
	# Heavier crates look a bit larger
	var scale_f := clampf(0.9 + mass_kg / 800.0, 0.9, 1.35)
	size *= scale_f

	var mesh := MeshInstance3D.new()
	var box := BoxMesh.new()
	box.size = size
	mesh.mesh = box
	var mat := StandardMaterial3D.new()
	mat.albedo_color = COLORS[color_idx % COLORS.size()]
	mat.roughness = 0.65
	mat.metallic = 0.05
	mesh.material_override = mat
	add_child(mesh)

	# Stripe so orientation is readable while swinging
	var stripe := MeshInstance3D.new()
	var stripe_mesh := BoxMesh.new()
	stripe_mesh.size = Vector3(size.x * 1.02, size.y * 0.18, size.z * 0.18)
	stripe.mesh = stripe_mesh
	var stripe_mat := StandardMaterial3D.new()
	stripe_mat.albedo_color = Color(0.95, 0.95, 0.9)
	stripe.material_override = stripe_mat
	add_child(stripe)

	var col := CollisionShape3D.new()
	var shape := BoxShape3D.new()
	shape.size = size
	col.shape = shape
	add_child(col)

	# Lift eye
	var eye := MeshInstance3D.new()
	var eye_mesh := TorusMesh.new()
	eye_mesh.inner_radius = 0.12
	eye_mesh.outer_radius = 0.2
	eye.mesh = eye_mesh
	eye.position.y = size.y * 0.5 + 0.05
	eye.rotation_degrees.x = 90
	var eye_mat := StandardMaterial3D.new()
	eye_mat.albedo_color = Color(0.55, 0.55, 0.58)
	eye.material_override = eye_mat
	add_child(eye)


func _physics_process(_delta: float) -> void:
	if is_held and _anchor:
		global_position = _anchor.global_position + _anchor.global_transform.basis * _follow_offset
		global_rotation = _anchor.global_rotation
		linear_velocity = Vector3.ZERO
		angular_velocity = Vector3.ZERO


func pick_up(anchor: Node3D) -> void:
	is_held = true
	_anchor = anchor
	freeze = true
	collision_layer = 0
	collision_mask = 0


func drop(at_pos: Vector3, velocity: Vector3) -> void:
	is_held = false
	_anchor = null
	freeze = false
	collision_layer = 2
	collision_mask = 1 | 8
	global_position = at_pos + Vector3(0.0, -0.85, 0.0)
	linear_velocity = velocity
	angular_velocity = Vector3(
		randf_range(-0.4, 0.4),
		randf_range(-0.4, 0.4),
		randf_range(-0.4, 0.4)
	)


func settle_on_pad() -> void:
	## Freeze in place after a successful delivery so the crate stays visible.
	is_held = false
	_anchor = null
	freeze = true
	collision_layer = 0
	collision_mask = 0
	linear_velocity = Vector3.ZERO
	angular_velocity = Vector3.ZERO
	set_meta("delivered", true)
