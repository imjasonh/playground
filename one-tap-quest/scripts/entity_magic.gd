class_name EntityMagic
extends Node2D

const DIRECTIONS: Array[Vector2] = [
	Vector2(-1, -1),
	Vector2(1, -1),
	Vector2(1, 1),
	Vector2(-1, 1),
]

var sprite: Sprite2D
var size := Vector2(12, 12)
var lv: int = 1
var valid: bool = true
var direction := Vector2.ZERO


func setup(dir_index: int, origin_center: Vector2, level: int) -> void:
	lv = level
	valid = true
	direction = DIRECTIONS[dir_index % DIRECTIONS.size()]
	position = origin_center - size * 0.5

	var s := GameData.thunder_scale_for_level(level)
	sprite = Sprite2D.new()
	sprite.centered = true
	sprite.position = size * 0.5
	sprite.scale = Vector2(s, s)
	sprite.texture = load("res://assets/sprites/magic_thunder.png")
	add_child(sprite)


func tick() -> void:
	if not valid:
		return
	position += direction


func get_rect() -> Rect2:
	return Rect2(position, size)


func is_inside_bounds(margin: float = 30.0) -> bool:
	if not valid:
		return false
	return (
		-margin <= position.x + size.x
		and position.x <= GameData.GAME_WIDTH + margin
		and -margin <= position.y + size.y
		and position.y <= GameData.GAME_HEIGHT + margin
	)


func destroy() -> void:
	valid = false
	visible = false
	position = Vector2(10000, 10000)
