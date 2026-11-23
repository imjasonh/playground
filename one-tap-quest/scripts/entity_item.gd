class_name EntityItem
extends Node2D

var sprite: Sprite2D
var item_name: String = ""
var size := Vector2(14, 14)
var valid: bool = true


func setup(kind: String, center_x: float, center_y: float) -> void:
	var data: Dictionary = GameData.ITEM_DATA[kind]
	item_name = kind
	valid = true
	position = Vector2(center_x - size.x * 0.5, center_y - size.y * 0.5)

	sprite = Sprite2D.new()
	sprite.centered = false
	sprite.texture = load(data["sprite"])
	add_child(sprite)


func get_rect() -> Rect2:
	return Rect2(position, size)


func get_center() -> Vector2:
	return position + size * 0.5


func destroy() -> void:
	valid = false
	visible = false
	position = Vector2(-1000, -1000)
