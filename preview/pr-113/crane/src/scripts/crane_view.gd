## Builds the physical tower-crane mesh hierarchy under $Crane.
extends Crane


func _ready() -> void:
	_assemble_crane()
	super._ready()


func _assemble_crane() -> void:
	# Tower
	var tower := _box(Vector3(1.6, 12.0, 1.6), Color(0.9, 0.72, 0.15), Vector3(0, 6, 0))
	add_child(tower)

	# Cab
	var cab := _box(Vector3(2.2, 1.6, 2.2), Color(0.2, 0.22, 0.25), Vector3(0, 12.2, 0))
	add_child(cab)

	# Counterweight jib (opposite boom)
	var counter := MeshInstance3D.new()
	var counter_mesh := BoxMesh.new()
	counter_mesh.size = Vector3(8.0, 0.5, 0.7)
	counter.mesh = counter_mesh
	counter.position = Vector3(-5.0, 12.6, 0)
	counter.material_override = _mat(Color(0.88, 0.7, 0.12))
	pivot.add_child(counter)

	var weight := _box(Vector3(2.5, 1.4, 1.4), Color(0.25, 0.27, 0.3), Vector3(-8.5, 12.3, 0))
	pivot.add_child(weight)

	# Main boom lattice look — long yellow beam
	var boom_beam := MeshInstance3D.new()
	var boom_mesh := BoxMesh.new()
	boom_mesh.size = Vector3(22.0, 0.55, 0.7)
	boom_beam.mesh = boom_mesh
	boom_beam.position = Vector3(11.0, 0.0, 0.0)
	boom_beam.material_override = _mat(Color(0.93, 0.75, 0.12))
	boom.add_child(boom_beam)

	# Boom top chord
	var chord := MeshInstance3D.new()
	var chord_mesh := BoxMesh.new()
	chord_mesh.size = Vector3(22.0, 0.2, 0.2)
	chord.mesh = chord_mesh
	chord.position = Vector3(11.0, 0.7, 0.0)
	chord.material_override = _mat(Color(0.85, 0.65, 0.1))
	boom.add_child(chord)

	# Position boom at tower top
	boom.position = Vector3(0, 12.8, 0)

	# Trolley carriage
	var carriage := _box(Vector3(1.2, 0.5, 1.0), Color(0.3, 0.32, 0.35), Vector3(0, -0.4, 0))
	carriage.name = "Carriage"
	trolley.add_child(carriage)
	trolley.position = Vector3(10.0, 0, 0)

	# Hook visual — clear only mesh children we own, keep Magnet
	for child in hook_body.get_children():
		if child is MeshInstance3D:
			child.queue_free()
	var hook_mesh := _box(Vector3(0.45, 0.7, 0.45), Color(0.85, 0.35, 0.12), Vector3.ZERO)
	hook_body.add_child(hook_mesh)
	var hook_ball := MeshInstance3D.new()
	var sphere := SphereMesh.new()
	sphere.radius = 0.22
	sphere.height = 0.44
	hook_ball.mesh = sphere
	hook_ball.position.y = -0.45
	hook_ball.material_override = _mat(Color(0.7, 0.2, 0.1))
	hook_body.add_child(hook_ball)

	# Ensure magnet area has a shape
	if magnet.get_child_count() == 0:
		var shape := CollisionShape3D.new()
		var sph := SphereShape3D.new()
		sph.radius = 1.1
		shape.shape = sph
		magnet.add_child(shape)

	# Ensure cable mesh exists after any rebuild
	if not is_instance_valid(cable_mesh):
		cable_mesh = MeshInstance3D.new()
		cable_mesh.name = "Cable"
		trolley.add_child(cable_mesh)
	if cable_mesh.mesh == null:
		var cyl := CylinderMesh.new()
		cyl.top_radius = 0.04
		cyl.bottom_radius = 0.04
		cyl.height = 1.0
		cable_mesh.mesh = cyl
	if cable_mesh.material_override == null:
		cable_mesh.material_override = _mat(Color(0.75, 0.78, 0.8))


func _box(size: Vector3, color: Color, pos: Vector3) -> MeshInstance3D:
	var mi := MeshInstance3D.new()
	var mesh := BoxMesh.new()
	mesh.size = size
	mi.mesh = mesh
	mi.position = pos
	mi.material_override = _mat(color)
	return mi


func _mat(color: Color) -> StandardMaterial3D:
	var mat := StandardMaterial3D.new()
	mat.albedo_color = color
	mat.roughness = 0.55
	mat.metallic = 0.25
	return mat
