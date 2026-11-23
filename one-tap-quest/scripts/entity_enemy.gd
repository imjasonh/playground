class_name EntityEnemy
extends Node2D

var sprite: Sprite2D
var enemy_name: String = ""
var size := Vector2(12, 12)
var lv: int = 1
var exp: int = 1
var interval: int = 20
var move_pattern: Array = []
var valid: bool = true

var _age: int = 0
var _velocity := Vector2.ZERO
var _next_move: int = 0


func setup(kind: String, center_x: float, center_y: float, rng: RandomNumberGenerator) -> void:
	var data: Dictionary = GameData.ENEMY_DATA[kind]
	enemy_name = kind
	size = Vector2(float(data["width"]), float(data["height"]))
	lv = int(data["lv"])
	exp = int(data["exp"])
	interval = int(data["interval"])
	move_pattern = data["move"]
	valid = true

	position = Vector2(center_x - size.x * 0.5, center_y - size.y * 0.5)
	_next_move = rng.randi_range(0, move_pattern.size() - 1)
	_age = 0
	_velocity = Vector2.ZERO

	sprite = Sprite2D.new()
	sprite.centered = false
	sprite.texture = load(data["sprite"])
	add_child(sprite)


func tick() -> void:
	if not valid:
		return
	_age += 1
	if (_age - 1) % interval == 0:
		var delta_move: Vector2 = move_pattern[_next_move]
		_velocity = delta_move / float(interval)
		_next_move = (_next_move + 1) % move_pattern.size()
	position += _velocity


func get_rect() -> Rect2:
	return Rect2(position, size)


func get_center() -> Vector2:
	return position + size * 0.5


func destroy() -> void:
	valid = false
	visible = false
	position = Vector2(-1000, -1000)
