extends Node2D

signal state_changed(lv: int, exp_points: int, score: int, status: String)

enum Phase { AIMING, FIELD, BOSS, GAME_OVER, GAME_CLEAR }

var phase: Phase = Phase.AIMING
var score: int = 0
var rng := RandomNumberGenerator.new()

var _world: Node2D
var _map_view: _TileGridView
var _aim_guide: _AimGuideView
var _entity_layer: Node2D
var _effect_layer: Node2D
var _hud_layer: Node2D
var _result_layer: Node2D

var _lv_label: Label
var _exp_label: Label
var _hint_label: Label

var player: EntityPlayer
var enemies: Array[EntityEnemy] = []
var items: Array[EntityItem] = []
var magics: Array[EntityMagic] = []
var effects: Array[EntityEffect] = []

var _boss_sprite: Sprite2D
var _boss_hp: int = GameData.BOSS_MAX_HP
var _boss_pos := Vector2.ZERO
var _boss_crystals: Array[Dictionary] = []
var _boss_defeated: bool = false
var _boss_clear_elapsed: float = 0.0
var _boss_explosions_spawned: int = 0
var _boss_result_shown: bool = false

var _tick_accum: float = 0.0
var _pause_timer: float = 0.0
var _game_over_timer: float = -1.0
var _killer_enemy: EntityEnemy = null
var _aim_dragging: bool = false

var _shake_target: Node2D = null
var _shake_origin := Vector2.ZERO
var _shake_size: float = 0.0
var _shake_remaining: float = 0.0
var _shake_step_accum: float = 0.0


func _ready() -> void:
	rng.randomize()
	_build_layers()
	new_game()


func _build_layers() -> void:
	_world = Node2D.new()
	add_child(_world)

	_map_view = _TileGridView.new()
	_world.add_child(_map_view)

	_aim_guide = _AimGuideView.new()
	_world.add_child(_aim_guide)

	_entity_layer = Node2D.new()
	_world.add_child(_entity_layer)

	_effect_layer = Node2D.new()
	_world.add_child(_effect_layer)

	_result_layer = Node2D.new()
	_world.add_child(_result_layer)

	_hud_layer = Node2D.new()
	add_child(_hud_layer)

	var hud_bg := ColorRect.new()
	hud_bg.color = Color(0, 0, 0, 1)
	hud_bg.position = Vector2.ZERO
	hud_bg.size = Vector2(GameData.GAME_WIDTH, GameData.HUD_HEIGHT)
	_hud_layer.add_child(hud_bg)

	_lv_label = _make_pixel_label(Vector2(4, 2), 9, Color(1, 1, 1))
	_hud_layer.add_child(_lv_label)

	_exp_label = _make_pixel_label(Vector2(96, 2), 9, Color(1, 1, 1))
	_hud_layer.add_child(_exp_label)

	_hint_label = _make_pixel_label(Vector2(174, 3), 8, Color(0.75, 0.85, 0.95))
	_hint_label.text = "TAP TO GO"
	_hud_layer.add_child(_hint_label)


func new_game() -> void:
	_clear_run()
	phase = Phase.AIMING
	score = 0
	_pause_timer = 0.0
	_game_over_timer = -1.0
	_killer_enemy = null
	_aim_dragging = false
	_boss_defeated = false
	_boss_clear_elapsed = 0.0
	_boss_explosions_spawned = 0
	_boss_result_shown = false
	_world.position = Vector2.ZERO
	_shake_target = null
	_shake_remaining = 0.0

	_map_view.set_map(GameData.FIELD_MAP)

	player = EntityPlayer.new()
	_spawn_items()
	_spawn_enemies()
	_entity_layer.add_child(player)

	_aim_guide.visible = true
	_aim_guide.set_aim_x(player.get_center().x)
	_hint_label.text = "DRAG & GO"
	_update_hud()
	_emit_state("aiming")


func _clear_run() -> void:
	for child in _entity_layer.get_children():
		child.queue_free()
	for child in _effect_layer.get_children():
		child.queue_free()
	for child in _result_layer.get_children():
		child.queue_free()
	enemies.clear()
	items.clear()
	magics.clear()
	effects.clear()
	_boss_crystals.clear()
	_boss_sprite = null
	player = null


func _spawn_items() -> void:
	# Upper band (y in [50, 150)), excluding "join"
	for item_name in GameData.ITEM_ORDER:
		if item_name == "join":
			continue
		var ix := float(GameData.rand_step(rng, GameData.GAME_WIDTH - 20, 10) + 10)
		var iy := float(GameData.rand_step(rng, 100, 10) + 50)
		var item := EntityItem.new()
		item.setup(item_name, ix, iy)
		_entity_layer.add_child(item)
		items.append(item)

	# Lower band (y in [150, 250)), including "join"
	for item_name in GameData.ITEM_ORDER:
		var ix := float(GameData.rand_step(rng, GameData.GAME_WIDTH - 20, 10) + 10)
		var iy := float(GameData.rand_step(rng, 100, 10) + 150)
		var item := EntityItem.new()
		item.setup(item_name, ix, iy)
		_entity_layer.add_child(item)
		items.append(item)


func _spawn_enemies() -> void:
	var spawned: Array[EntityEnemy] = []
	for layer_idx in range(GameData.LAYER_MONSTER_TYPES.size()):
		var pool: Array = GameData.LAYER_MONSTER_TYPES[layer_idx]
		var count: int = GameData.LAYER_MONSTER_NUM[layer_idx]
		var base_y: int = GameData.LAYER_HEIGHT[layer_idx][0]
		var range_y: int = GameData.LAYER_HEIGHT[layer_idx][1]
		for _i in range(count):
			var kind: String = pool[rng.randi_range(0, pool.size() - 1)]
			var ex := float(GameData.rand_step(rng, GameData.GAME_WIDTH - 20, 10) + 10)
			var ey := float(base_y + GameData.rand_step(rng, range_y, 10))
			var enemy := EntityEnemy.new()
			enemy.setup(kind, ex, ey, rng)
			spawned.append(enemy)

	# Y-sort back-to-front by bottom edge (matches original Enchant.js sort).
	spawned.sort_custom(func(a: EntityEnemy, b: EntityEnemy) -> bool:
		return (a.position.y + a.size.y) < (b.position.y + b.size.y)
	)
	for enemy in spawned:
		_entity_layer.add_child(enemy)
		enemies.append(enemy)


func _unhandled_input(event: InputEvent) -> void:
	if event is InputEventMouseButton:
		var mb := event as InputEventMouseButton
		if mb.button_index != MOUSE_BUTTON_LEFT:
			return
		var pos := _to_game_pos(mb.position)
		if mb.pressed:
			if phase == Phase.AIMING:
				_aim_dragging = true
				_set_player_aim_x(pos.x)
			else:
				new_game()
		else:
			if phase == Phase.AIMING and _aim_dragging:
				_aim_dragging = false
				_launch_player()
	elif event is InputEventMouseMotion:
		if phase == Phase.AIMING and _aim_dragging:
			var mm := event as InputEventMouseMotion
			_set_player_aim_x(_to_game_pos(mm.position).x)


func _to_game_pos(screen_pos: Vector2) -> Vector2:
	return get_canvas_transform().affine_inverse() * screen_pos


func _set_player_aim_x(world_x: float) -> void:
	if player == null:
		return
	player.position.x = clampf(roundf(world_x - player.size.x * 0.5), 0.0, GameData.GAME_WIDTH - player.size.x)
	_aim_guide.set_aim_x(player.get_center().x)


func _launch_player() -> void:
	phase = Phase.FIELD
	player.valid = true
	_aim_guide.visible = false
	_hint_label.text = "TAP=RETRY"
	_emit_state("playing")


func _process(delta: float) -> void:
	_update_shake(delta)

	if _game_over_timer >= 0.0:
		_game_over_timer -= delta
		if _game_over_timer <= 0.0:
			_game_over_timer = -1.0
			_show_result("GAME OVER")
			if _killer_enemy != null:
				_show_enemy_level(_killer_enemy)

	if _boss_defeated:
		_update_boss_clear_sequence(delta)

	if _pause_timer > 0.0:
		_pause_timer = maxf(0.0, _pause_timer - delta)

	_tick_accum += delta
	var step := 1.0 / GameData.TICK_FPS
	while _tick_accum >= step:
		_tick_accum -= step
		_step_24fps()


func _step_24fps() -> void:
	_tick_effects()

	if phase == Phase.BOSS:
		_tick_boss_crystals()

	if _pause_timer > 0.0:
		return

	match phase:
		Phase.AIMING:
			for enemy in enemies:
				enemy.tick()
		Phase.FIELD:
			for enemy in enemies:
				enemy.tick()
			for magic in magics:
				magic.tick()
			player.tick()
			_check_field_collisions()
		Phase.BOSS:
			if not _boss_defeated:
				player.tick()
				_check_boss_collision()
		Phase.GAME_OVER, Phase.GAME_CLEAR:
			pass


func _tick_effects() -> void:
	var idx := effects.size() - 1
	while idx >= 0:
		var fx := effects[idx]
		if not fx.tick():
			fx.queue_free()
			effects.remove_at(idx)
		idx -= 1


func _check_field_collisions() -> void:
	var p_rect := player.get_rect()

	# 1. Player vs Enemies
	for enemy in enemies:
		if enemy.valid and p_rect.intersects(enemy.get_rect()):
			_pause_timer = maxf(_pause_timer, 0.2)
			if player.lv >= enemy.lv:
				player.position.y += 5.0
				_kill_enemy(enemy)
			else:
				_trigger_game_over(enemy)
				return

	# 2. Player vs Items
	p_rect = player.get_rect()
	for item in items:
		if item.valid and p_rect.intersects(item.get_rect()):
			_apply_item(item)
			_pause_timer = maxf(_pause_timer, 0.5)
			p_rect = player.get_rect()

	# 3. Magic vs Enemies
	for enemy in enemies:
		if not enemy.valid:
			continue
		var e_rect := enemy.get_rect()
		for magic in magics:
			if magic.valid and magic.get_rect().intersects(e_rect):
				if magic.lv >= enemy.lv:
					_pause_timer = maxf(_pause_timer, 0.2)
					_kill_enemy(enemy)
					break
				else:
					magic.destroy()

	# 4. Boss transition
	if player.position.y < -30.0 and _all_magics_out():
		_enter_boss_stage()


func _kill_enemy(enemy: EntityEnemy) -> void:
	var center := enemy.get_center()
	_spawn_effect(EntityEffect.create_kill(enemy.size.y, center))
	_spawn_effect(EntityEffect.create_exp(enemy.exp, center))
	var exp_gain := enemy.exp
	enemy.destroy()
	score += exp_gain
	_give_player_exp(exp_gain)


func _give_player_exp(amount: int) -> void:
	var gained := player.give_exp(amount)
	for _i in range(gained):
		_spawn_effect(EntityEffect.create_lvup(player.get_center()))
	_update_hud()
	_emit_state("playing")


func _apply_item(item: EntityItem) -> void:
	var center := item.get_center()
	match item.item_name:
		"sword", "shield":
			_give_player_exp(GameData.exp_to_next_level(player.lv, player.exp))
		"join":
			_give_player_exp(GameData.exp_to_next_level(player.lv, player.exp))
			player.join_party()
		"warp":
			player.position = GameData.compute_warp_position(player.position, player.size.x)
		"thunder":
			for dir_idx in range(4):
				var orb := EntityMagic.new()
				orb.setup(dir_idx, center, player.lv)
				_entity_layer.add_child(orb)
				magics.append(orb)

	_spawn_effect(EntityEffect.create_item(center))
	item.destroy()


func _all_magics_out() -> bool:
	for magic in magics:
		if magic.is_inside_bounds(30.0):
			return false
	return true


func _enter_boss_stage() -> void:
	phase = Phase.BOSS

	# Clear field entities except player
	for enemy in enemies:
		enemy.queue_free()
	enemies.clear()
	for item in items:
		item.queue_free()
	items.clear()
	for magic in magics:
		magic.queue_free()
	magics.clear()

	_map_view.set_map(GameData.BOSS_MAP)

	player.position = Vector2(roundf(GameData.GAME_WIDTH / 2.0 - player.size.x / 2.0) + 2.0, 220.0)
	_pause_timer = 1.0

	_boss_hp = GameData.BOSS_MAX_HP
	_boss_sprite = Sprite2D.new()
	_boss_sprite.centered = false
	_boss_sprite.texture = load("res://assets/sprites/enemy_boss.png")
	_boss_pos = Vector2(roundf(GameData.GAME_WIDTH / 2.0 - 20.0), roundf(GameData.GAME_HEIGHT / 2.0 - 20.0))
	_boss_sprite.position = _boss_pos
	_entity_layer.add_child(_boss_sprite)

	var boss_center := _boss_pos + Vector2(20, 20)
	var crystal_tex: Texture2D = load("res://assets/sprites/boss_crystal.png")
	var shadow_tex: Texture2D = load("res://assets/sprites/boss_crystal_shadow.png")

	for i in range(_boss_hp):
		var cpos := GameData.boss_crystal_position(i, _boss_hp, boss_center)
		var group := Node2D.new()
		var shadow := Sprite2D.new()
		shadow.centered = false
		shadow.texture = shadow_tex
		shadow.position = Vector2(cpos.x - 6.0, cpos.y - 8.0 + 22.0)
		group.add_child(shadow)

		var crystal := Sprite2D.new()
		crystal.centered = false
		crystal.texture = crystal_tex
		crystal.position = Vector2(cpos.x - 6.0, cpos.y - 8.0)
		group.add_child(crystal)

		_entity_layer.add_child(group)
		_boss_crystals.append({
			"group": group,
			"crystal": crystal,
			"base_y": crystal.position.y,
			"age": i * 20,
		})

	_emit_state("boss")


func _tick_boss_crystals() -> void:
	for entry in _boss_crystals:
		entry["age"] = int(entry["age"]) + 1
		var c: Sprite2D = entry["crystal"]
		c.position.y = float(entry["base_y"]) + cos(float(entry["age"]) / 20.0) * 5.0


func _check_boss_collision() -> void:
	if _boss_sprite == null:
		return
	var boss_rect := Rect2(_boss_pos, Vector2(40, 40))
	if not player.get_rect().intersects(boss_rect):
		return

	if player.lv > 1:
		_boss_hp -= 1
		player.lv -= 1
		player.position.y += 6.0
		_start_shake(_boss_sprite, _boss_pos, 6.0, 0.16)
		if not _boss_crystals.is_empty():
			var first: Dictionary = _boss_crystals.pop_front()
			var c: Sprite2D = first["crystal"]
			_spawn_effect(EntityEffect.create_kill(12.0, c.position + Vector2(6, 8)))
			var g: Node2D = first["group"]
			g.queue_free()
		_pause_timer = 0.5
		_update_hud()
		_emit_state("boss")

		if _boss_hp <= 0:
			_boss_defeated = true
			_boss_clear_elapsed = 0.0
			_boss_explosions_spawned = 0
			_boss_result_shown = false
			player.valid = false
			score += GameData.BOSS_CLEAR_BONUS
			_emit_state("clear")
	else:
		player.lv = 0
		player.position.y += 10.0
		_update_hud()
		_trigger_game_over(null)


func _update_boss_clear_sequence(delta: float) -> void:
	_boss_clear_elapsed += delta
	if _boss_clear_elapsed >= 2.0 and _boss_explosions_spawned == 0 and _boss_sprite != null:
		_start_shake(_boss_sprite, _boss_pos, 2.0, 4.0)

	if _boss_clear_elapsed >= 2.0 and _boss_explosions_spawned < 20:
		var target_count := mini(20, int(floor((_boss_clear_elapsed - 2.0) / 0.12)) + 1)
		while _boss_explosions_spawned < target_count:
			var rx := _boss_pos.x + float(rng.randi_range(0, 39))
			var ry := _boss_pos.y + float(rng.randi_range(0, 39))
			_spawn_effect(EntityEffect.create_kill(16.0, Vector2(rx, ry)))
			_boss_explosions_spawned += 1

	if _boss_clear_elapsed >= 4.0 and _boss_sprite != null and _boss_sprite.visible:
		_boss_sprite.visible = false

	if _boss_clear_elapsed >= 6.0 and not _boss_result_shown:
		_boss_result_shown = true
		phase = Phase.GAME_CLEAR
		_show_result("GAME CLEAR!")


func _trigger_game_over(killer: EntityEnemy) -> void:
	phase = Phase.GAME_OVER
	player.fall_over()
	_killer_enemy = killer
	_game_over_timer = 1.5
	_start_shake(_world, Vector2.ZERO, 4.0, 0.08)
	_emit_state("game_over")


func _start_shake(target: Node2D, origin: Vector2, amount: float, duration: float) -> void:
	if _shake_target != null and is_instance_valid(_shake_target):
		_shake_target.position = _shake_origin
	_shake_target = target
	_shake_origin = origin
	_shake_size = amount
	_shake_remaining = duration
	_shake_step_accum = 0.0


func _update_shake(delta: float) -> void:
	if _shake_target == null or not is_instance_valid(_shake_target):
		_shake_target = null
		return
	if _shake_remaining <= 0.0:
		return
	_shake_remaining -= delta
	_shake_step_accum += delta
	if _shake_remaining <= 0.0:
		_shake_target.position = _shake_origin
		_shake_target = null
	elif _shake_step_accum >= 0.02:
		_shake_step_accum = 0.0
		var ox := float(rng.randi_range(0, int(_shake_size))) - roundf(_shake_size * 0.5)
		var oy := float(rng.randi_range(0, int(_shake_size))) - roundf(_shake_size * 0.5)
		_shake_target.position = _shake_origin + Vector2(ox, oy)


func _spawn_effect(fx: EntityEffect) -> void:
	_effect_layer.add_child(fx)
	effects.append(fx)


func _show_result(title: String) -> void:
	var panel := ColorRect.new()
	panel.color = Color(0, 0, 0, 0.72)
	panel.position = Vector2(25, 112)
	panel.size = Vector2(200, 62)
	_result_layer.add_child(panel)

	var title_lbl := _make_centered_label(title, 120.0, 14, Color(1.0, 0.92, 0.35) if title == "GAME CLEAR!" else Color(1.0, 0.45, 0.45))
	_result_layer.add_child(title_lbl)

	var score_lbl := _make_centered_label("SCORE %d" % (score * GameData.SCORE_MULTIPLIER), 140.0, 11, Color(1, 1, 1))
	_result_layer.add_child(score_lbl)

	var retry_lbl := _make_centered_label("TAP TO PLAY AGAIN", 158.0, 8, Color(0.8, 0.85, 0.95))
	_result_layer.add_child(retry_lbl)


func _show_enemy_level(enemy: EntityEnemy) -> void:
	var c := enemy.get_center()
	var lbl := _make_pixel_label(Vector2(c.x - 14.0, c.y + 4.0), 9, Color(1, 1, 1))
	lbl.text = "LV %d" % enemy.lv
	lbl.add_theme_color_override("font_outline_color", Color(0, 0, 0))
	lbl.add_theme_constant_override("outline_size", 3)
	_result_layer.add_child(lbl)


func _make_pixel_label(pos: Vector2, font_size: int, color: Color) -> Label:
	var lbl := Label.new()
	lbl.position = pos
	lbl.add_theme_font_size_override("font_size", font_size)
	lbl.add_theme_color_override("font_color", color)
	return lbl


func _make_centered_label(text: String, y: float, font_size: int, color: Color) -> Label:
	var lbl := Label.new()
	lbl.text = text
	lbl.position = Vector2(0, y)
	lbl.size = Vector2(GameData.GAME_WIDTH, 20)
	lbl.horizontal_alignment = HORIZONTAL_ALIGNMENT_CENTER
	lbl.add_theme_font_size_override("font_size", font_size)
	lbl.add_theme_color_override("font_color", color)
	lbl.add_theme_color_override("font_outline_color", Color(0, 0, 0))
	lbl.add_theme_constant_override("outline_size", 3)
	return lbl


func _update_hud() -> void:
	if player == null:
		return
	_lv_label.text = "LV%d" % player.lv
	_exp_label.text = "EXP%d" % player.exp


func _emit_state(status: String) -> void:
	var lv := player.lv if player != null else 1
	var xp := player.exp if player != null else 0
	state_changed.emit(lv, xp, score * GameData.SCORE_MULTIPLIER, status)


class _TileGridView extends Node2D:
	var _tiles_tex: Texture2D
	var _grid: Array = []

	func _init() -> void:
		_tiles_tex = load("res://assets/tiles/map_tiles.png")

	func set_map(grid: Array) -> void:
		_grid = grid
		queue_redraw()

	func _draw() -> void:
		if _tiles_tex == null or _grid.is_empty():
			return
		for row in range(_grid.size()):
			var line: Array = _grid[row]
			for col in range(line.size()):
				var tile_id: int = line[col]
				var src := Rect2(float(tile_id * 16), 0.0, 16.0, 16.0)
				var dst := Rect2(float(col * 16 - 10), float(row * 16), 16.0, 16.0)
				draw_texture_rect_region(_tiles_tex, dst, src)


class _AimGuideView extends Node2D:
	var _aim_x: float = 125.0

	func set_aim_x(x: float) -> void:
		_aim_x = x
		queue_redraw()

	func _draw() -> void:
		var y := float(GameData.GAME_HEIGHT - 16)
		while y > float(GameData.HUD_HEIGHT + 4):
			draw_line(
				Vector2(_aim_x, y),
				Vector2(_aim_x, maxf(float(GameData.HUD_HEIGHT + 4), y - 4.0)),
				Color(1.0, 1.0, 1.0, 0.35),
				1.0
			)
			y -= 8.0
