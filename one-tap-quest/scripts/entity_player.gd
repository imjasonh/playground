class_name EntityPlayer
extends Node2D

var sprite: Sprite2D
var size := Vector2(12, 12)
var lv: int = 1
var exp: int = 0
var speed: float = GameData.PLAYER_SPEED
var valid: bool = false
var is_party: bool = false
var dead: bool = false

var _tex_solo: Texture2D
var _tex_party: Texture2D


func _init() -> void:
	_tex_solo = load("res://assets/sprites/player.png")
	_tex_party = load("res://assets/sprites/player_party.png")

	sprite = Sprite2D.new()
	sprite.centered = false
	sprite.texture = _tex_solo
	add_child(sprite)

	reset()


func reset() -> void:
	lv = 1
	exp = 0
	speed = GameData.PLAYER_SPEED
	valid = false
	is_party = false
	dead = false
	size = Vector2(12, 12)
	sprite.texture = _tex_solo
	sprite.rotation = 0.0
	sprite.position = Vector2.ZERO
	position = Vector2(roundf(GameData.GAME_WIDTH / 2.0), GameData.GAME_HEIGHT - size.y - 1.0)


func tick() -> void:
	if valid and not dead:
		position.y -= speed


func get_rect() -> Rect2:
	return Rect2(position, size)


func get_center() -> Vector2:
	return position + size * 0.5


func join_party() -> void:
	if is_party:
		return
	is_party = true
	position.x -= 12.0
	size = Vector2(36, 12)
	sprite.texture = _tex_party


func give_exp(amount: int) -> int:
	var result := GameData.apply_exp(lv, exp, amount)
	lv = result["lv"]
	exp = result["exp"]
	return result["levels_gained"]


func fall_over() -> void:
	dead = true
	valid = false
	sprite.rotation = PI * 0.5
	sprite.position = Vector2(size.x, 0.0)
