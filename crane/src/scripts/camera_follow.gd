## Orbit camera that slowly tracks the trolley for a better view of the lift.
extends Camera3D

@onready var crane: Crane = $"../../Crane"

var _look_target := Vector3(0, 4, 0)


func _ready() -> void:
	look_at(_look_target, Vector3.UP)


func _process(delta: float) -> void:
	if crane == null:
		return
	var trolley: Node3D = crane.get_node_or_null("Pivot/Boom/Trolley")
	var pivot: Node3D = crane.get_node_or_null("Pivot")
	if trolley == null or pivot == null:
		return
	var focus: Vector3 = trolley.global_position
	focus.y = maxf(focus.y - 4.0, 2.0)
	_look_target = _look_target.lerp(focus, 1.0 - exp(-2.0 * delta))
	var yaw: float = pivot.rotation.y
	var radius := 28.0
	var height := 20.0
	var desired := Vector3(cos(yaw - 0.9) * radius, height, sin(yaw - 0.9) * radius)
	global_position = global_position.lerp(desired, 1.0 - exp(-1.2 * delta))
	look_at(_look_target, Vector3.UP)
