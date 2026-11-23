class_name EntityEffect
extends Node2D

enum Kind { KILL, ITEM, EXP, LVUP }

var kind: Kind
var _age: int = 0
var _sprite: Sprite2D
var _label: Label
var _anim_interval: int = 2
var _total_frames: int = 5


static func create_kill(target_height: float, center: Vector2) -> EntityEffect:
	var fx := EntityEffect.new()
	fx.kind = Kind.KILL
	fx._anim_interval = 2
	fx._total_frames = 5
	fx.position = center

	var s := Sprite2D.new()
	s.texture = load("res://assets/sprites/effect_kill.png")
	s.hframes = 5
	s.frame = 0
	var scale_factor := target_height / 10.0
	s.scale = Vector2(scale_factor, scale_factor)
	fx.add_child(s)
	fx._sprite = s
	return fx


static func create_item(center: Vector2) -> EntityEffect:
	var fx := EntityEffect.new()
	fx.kind = Kind.ITEM
	fx._anim_interval = 3
	fx._total_frames = 4
	fx.position = center

	var s := Sprite2D.new()
	s.texture = load("res://assets/sprites/effect_item.png")
	s.hframes = 4
	s.frame = 0
	fx.add_child(s)
	fx._sprite = s
	return fx


static func create_exp(exp_amount: int, center: Vector2) -> EntityEffect:
	var fx := EntityEffect.new()
	fx.kind = Kind.EXP
	fx.position = center + Vector2(-18, -6)

	var lbl := Label.new()
	lbl.text = "+%d EXP" % exp_amount
	lbl.add_theme_font_size_override("font_size", 8)
	lbl.add_theme_color_override("font_color", Color(1.0, 0.95, 0.45))
	lbl.add_theme_color_override("font_outline_color", Color(0, 0, 0))
	lbl.add_theme_constant_override("outline_size", 2)
	fx.add_child(lbl)
	fx._label = lbl
	return fx


static func create_lvup(center: Vector2) -> EntityEffect:
	var fx := EntityEffect.new()
	fx.kind = Kind.LVUP
	fx.position = center + Vector2(0, 6)
	fx.scale = Vector2(1.6, 1.6)

	var lbl := Label.new()
	lbl.text = "LV UP!"
	lbl.position = Vector2(-16, -6)
	lbl.add_theme_font_size_override("font_size", 8)
	lbl.add_theme_color_override("font_color", Color(0.45, 0.95, 1.0))
	lbl.add_theme_color_override("font_outline_color", Color(0, 0, 0))
	lbl.add_theme_constant_override("outline_size", 2)
	fx.add_child(lbl)
	fx._label = lbl
	return fx


func tick() -> bool:
	_age += 1
	match kind:
		Kind.KILL, Kind.ITEM:
			var frame_idx := _age / _anim_interval
			if frame_idx >= _total_frames:
				return false
			_sprite.frame = frame_idx
		Kind.EXP:
			if _age < 7:
				position.y -= 2.0
			if _age > 20:
				return false
		Kind.LVUP:
			if _age < 7:
				scale -= Vector2(0.1, 0.1)
			if _age > 20:
				return false
	return true
