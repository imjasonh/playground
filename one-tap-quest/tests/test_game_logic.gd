extends SceneTree

var _failures: int = 0
var _tests_run: int = 0


var _started: bool = false


func _process(_delta: float) -> bool:
	if _started:
		return true
	_started = true
	_run_all()
	if _failures > 0:
		push_error("%d test(s) failed out of %d" % [_failures, _tests_run])
		quit(1)
	else:
		print("PASS: %d One Tap Quest tests passed" % _tests_run)
		quit(0)
	return true


func _assert_eq(actual: Variant, expected: Variant, label: String) -> void:
	_tests_run += 1
	if actual != expected:
		_failures += 1
		push_error("FAIL [%s]: expected %s, got %s" % [label, str(expected), str(actual)])


func _assert_true(cond: bool, label: String) -> void:
	_tests_run += 1
	if not cond:
		_failures += 1
		push_error("FAIL [%s]: expected true" % label)


func _run_all() -> void:
	_test_level_curve()
	_test_warp_math()
	_test_thunder_scale()
	_test_boss_crystals()
	_test_player_party()
	_test_enemy_patrol()
	_test_main_scene_spawns_and_combat()
	_test_boss_threshold()


func _test_level_curve() -> void:
	var r1 := GameData.apply_exp(1, 0, 1)
	_assert_eq(r1["lv"], 1, "1 exp stays lv 1")
	_assert_eq(r1["levels_gained"], 0, "no level up at 1 exp")

	var r2 := GameData.apply_exp(1, 0, 2)
	_assert_eq(r2["lv"], 2, "2 exp reaches lv 2")
	_assert_eq(r2["levels_gained"], 1, "gained 1 level")

	var r3 := GameData.apply_exp(1, 0, 10)
	_assert_eq(r3["lv"], 5, "10 exp reaches lv 5")
	_assert_eq(r3["levels_gained"], 4, "gained 4 levels at once")

	_assert_eq(GameData.exp_to_next_level(1, 1), 1, "lv1 with 1 exp needs 1 more")
	_assert_eq(GameData.exp_to_next_level(2, 2), 2, "lv2 with 2 exp needs 2 more")


func _test_warp_math() -> void:
	var normal := GameData.compute_warp_position(Vector2(50, 100), 12)
	_assert_eq(normal, Vector2(130, 140), "warp shifts +80x, +40y")

	var near_right := GameData.compute_warp_position(Vector2(200, 100), 12)
	_assert_eq(near_right, Vector2(120, 140), "warp near right edge wraps -80x")


func _test_thunder_scale() -> void:
	_assert_eq(GameData.thunder_scale_for_level(1), 0.6, "lv1 thunder clamped to 0.6")
	_assert_eq(GameData.thunder_scale_for_level(4), 0.8, "lv4 thunder is 0.8")
	_assert_eq(GameData.thunder_scale_for_level(10), 1.0, "lv10 thunder clamped to 1.0")


func _test_boss_crystals() -> void:
	var center := Vector2(125, 150)
	for i in range(GameData.BOSS_MAX_HP):
		var pos := GameData.boss_crystal_position(i, GameData.BOSS_MAX_HP, center)
		var dist := pos.distance_to(center)
		_assert_true(absf(dist - 80.0) <= 1.5, "crystal %d sits on radius 80" % i)


func _test_player_party() -> void:
	var p := EntityPlayer.new()
	_assert_eq(p.size, Vector2(12, 12), "solo hero width is 12")
	var orig_x := p.position.x
	p.join_party()
	_assert_eq(p.size, Vector2(36, 12), "party width expands to 36")
	_assert_eq(p.position.x, orig_x - 12.0, "party centers on hero")
	p.join_party()
	_assert_eq(p.size, Vector2(36, 12), "second join is idempotent")
	p.free()


func _test_enemy_patrol() -> void:
	var rng := RandomNumberGenerator.new()
	rng.seed = 42
	var e := EntityEnemy.new()
	e.setup("slime", 100.0, 200.0, rng)
	var start_pos := e.position
	# Full slime cycle = 6 steps * 20 ticks = 120 ticks returns to start.
	for _i in range(120):
		e.tick()
	_assert_true(e.position.distance_to(start_pos) < 0.01, "slime patrol closes loop after 120 ticks")
	e.free()


func _test_main_scene_spawns_and_combat() -> void:
	var main_scene: PackedScene = load("res://scenes/main.tscn")
	var main: Node2D = main_scene.instantiate()
	root.add_child(main)

	_assert_eq(main.enemies.size(), 49, "spawns 49 enemies (24+18+7)")
	_assert_eq(main.items.size(), 9, "spawns 9 items (4 upper + 5 lower)")

	var join_count := 0
	for item in main.items:
		if item.item_name == "join":
			join_count += 1
	_assert_eq(join_count, 1, "exactly one join item per run")

	# Launching sets phase to FIELD and enables player movement.
	main._launch_player()
	_assert_eq(main.phase, main.Phase.FIELD, "launch transitions to FIELD")
	_assert_true(main.player.valid, "player becomes active after launch")

	# Defeating a LV 1 slime at LV 1 succeeds and grants 1 EXP & 1 score.
	var slime := EntityEnemy.new()
	slime.setup("slime", main.player.get_center().x, main.player.get_center().y, main.rng)
	main._entity_layer.add_child(slime)
	main.enemies.append(slime)
	main._check_field_collisions()
	_assert_true(not slime.valid, "lv1 player defeats lv1 slime")
	_assert_eq(main.score, 1, "defeating slime adds 1 score")

	# Fighting a LV 10 dragon at LV 1 triggers GAME_OVER.
	var dragon := EntityEnemy.new()
	dragon.setup("dragon", main.player.get_center().x, main.player.get_center().y, main.rng)
	main._entity_layer.add_child(dragon)
	main.enemies.append(dragon)
	main._check_field_collisions()
	_assert_eq(main.phase, main.Phase.GAME_OVER, "lv1 player loses to lv10 dragon")

	main.free()


func _test_boss_threshold() -> void:
	var main_scene: PackedScene = load("res://scenes/main.tscn")
	var main: Node2D = main_scene.instantiate()
	root.add_child(main)

	# LV 10 entering boss room defeats all 9 crystals and survives at LV 1.
	main._launch_player()
	main.player.lv = 10
	main._enter_boss_stage()
	_assert_eq(main.phase, main.Phase.BOSS, "entered BOSS phase")
	_assert_eq(main._boss_hp, 9, "boss starts with 9 HP")

	for _hit in range(9):
		main.player.position = main._boss_pos + Vector2(10, 10)
		main._check_boss_collision()
	_assert_eq(main._boss_hp, 0, "lv10 hero depletes all 9 boss HP")
	_assert_eq(main.player.lv, 1, "lv10 hero finishes boss at lv1")
	_assert_true(main._boss_defeated, "boss marked defeated")
	_assert_eq(main.score, GameData.BOSS_CLEAR_BONUS, "boss clear adds 100 score bonus")

	# LV 9 entering boss room dies on the 9th collision.
	main.new_game()
	main._launch_player()
	main.player.lv = 9
	main._enter_boss_stage()
	for _hit in range(9):
		if main.phase == main.Phase.GAME_OVER:
			break
		main.player.position = main._boss_pos + Vector2(10, 10)
		main._check_boss_collision()
	_assert_eq(main.phase, main.Phase.GAME_OVER, "lv9 hero cannot finish 9-HP boss")
	_assert_eq(main.player.lv, 0, "defeated hero drops to lv0")

	main.free()
