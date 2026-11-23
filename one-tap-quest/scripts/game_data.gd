class_name GameData
extends RefCounted

const GAME_WIDTH := 250
const GAME_HEIGHT := 300
const HUD_HEIGHT := 16
const TICK_FPS := 24.0
const PLAYER_SPEED := 1.0
const BOSS_MAX_HP := 9
const BOSS_CLEAR_BONUS := 100
const SCORE_MULTIPLIER := 100

# Cumulative EXP required to advance from level `lv` to `lv + 1`.
const NEXT_LEVEL_EXP: Array[int] = [
	0,
	2,
	4,
	7,
	10,
	14,
	20,
	26,
	32,
	38,
	46,
	52,
	58,
	66,
	72,
	80,
	90,
	100,
	110,
	120,
	130,
	140,
	150,
	999,
]

const ENEMY_DATA: Dictionary = {
	"slime": {
		"sprite": "res://assets/sprites/enemy_slime.png",
		"width": 12,
		"height": 12,
		"lv": 1,
		"exp": 1,
		"interval": 20,
		"move": [
			Vector2(10, 0),
			Vector2(0, 0),
			Vector2(-10, 0),
			Vector2(-10, 0),
			Vector2(0, 0),
			Vector2(10, 0),
		],
	},
	"snake": {
		"sprite": "res://assets/sprites/enemy_snake.png",
		"width": 12,
		"height": 12,
		"lv": 2,
		"exp": 2,
		"interval": 20,
		"move": [
			Vector2(-15, 0),
			Vector2(15, 0),
			Vector2(15, 0),
			Vector2(-15, 0),
		],
	},
	"bandit": {
		"sprite": "res://assets/sprites/enemy_bandit.png",
		"width": 14,
		"height": 14,
		"lv": 3,
		"exp": 3,
		"interval": 20,
		"move": [
			Vector2(-20, 0),
			Vector2(20, -10),
			Vector2(20, 10),
			Vector2(-20, 0),
			Vector2(0, 0),
		],
	},
	"goblin": {
		"sprite": "res://assets/sprites/enemy_goblin.png",
		"width": 14,
		"height": 14,
		"lv": 6,
		"exp": 4,
		"interval": 10,
		"move": [
			Vector2(10, 0),
			Vector2(0, 0),
			Vector2(10, 0),
			Vector2(0, 0),
			Vector2(-10, 0),
			Vector2(0, 0),
			Vector2(-10, 0),
			Vector2(0, 0),
			Vector2(-10, 0),
			Vector2(0, 0),
			Vector2(-10, 0),
			Vector2(0, 0),
			Vector2(10, 0),
			Vector2(0, 0),
			Vector2(10, 0),
		],
	},
	"golem": {
		"sprite": "res://assets/sprites/enemy_golem.png",
		"width": 16,
		"height": 16,
		"lv": 7,
		"exp": 5,
		"interval": 80,
		"move": [
			Vector2(20, 0),
			Vector2(-20, 0),
			Vector2(-20, 0),
			Vector2(20, 0),
		],
	},
	"minotaur": {
		"sprite": "res://assets/sprites/enemy_minotaur.png",
		"width": 16,
		"height": 16,
		"lv": 8,
		"exp": 6,
		"interval": 40,
		"move": [
			Vector2(10, 0),
			Vector2(-10, 0),
			Vector2(-10, 0),
			Vector2(10, 0),
		],
	},
	"iron": {
		"sprite": "res://assets/sprites/enemy_iron.png",
		"width": 20,
		"height": 20,
		"lv": 9,
		"exp": 7,
		"interval": 40,
		"move": [
			Vector2(15, 0),
			Vector2(0, 0),
			Vector2(0, 0),
			Vector2(0, 0),
			Vector2(-15, 0),
			Vector2(-15, 0),
			Vector2(0, 0),
			Vector2(0, 0),
			Vector2(0, 0),
			Vector2(15, 0),
		],
	},
	"dragon": {
		"sprite": "res://assets/sprites/enemy_dragon.png",
		"width": 32,
		"height": 24,
		"lv": 10,
		"exp": 10,
		"interval": 240,
		"move": [
			Vector2(30, 0),
			Vector2(-30, 0),
		],
	},
}

const LAYER_MONSTER_TYPES: Array = [
	["slime", "slime", "slime", "slime", "slime", "slime", "slime", "slime", "snake", "snake", "snake", "bandit"],
	["slime", "snake", "bandit", "bandit", "bandit", "bandit", "goblin", "goblin", "goblin", "golem", "golem"],
	["dragon", "iron", "iron", "minotaur", "minotaur"],
]

const LAYER_MONSTER_NUM: Array[int] = [24, 18, 7]

# [base_y, height_range]
const LAYER_HEIGHT: Array = [
	[180, 80],
	[90, 80],
	[25, 40],
]

const ITEM_DATA: Dictionary = {
	"sword": {"sprite": "res://assets/sprites/item_sword.png"},
	"shield": {"sprite": "res://assets/sprites/item_shield.png"},
	"thunder": {"sprite": "res://assets/sprites/item_thunder.png"},
	"warp": {"sprite": "res://assets/sprites/item_warp.png"},
	"join": {"sprite": "res://assets/sprites/item_join.png"},
}

const ITEM_ORDER: Array[String] = ["sword", "shield", "thunder", "warp", "join"]

# Tile indices matching assets/tiles/map_tiles.png:
# 0: grass, 1: grass_flower, 2: sand_path, 3: water, 4: stone_floor, 5: castle_wall
const FIELD_MAP: Array = [
	[5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5],
	[5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5],
	[5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
	[5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5],
	[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
	[0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 3, 3, 0, 0],
	[1, 0, 0, 0, 0, 0, 0, 0, 0, 3, 3, 3, 3, 3, 3, 0, 0],
	[0, 0, 0, 0, 2, 2, 2, 0, 0, 3, 3, 3, 3, 0, 2, 2, 2],
	[0, 0, 2, 2, 2, 2, 2, 2, 2, 0, 0, 0, 2, 2, 2, 2, 2],
	[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
	[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
	[2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2, 2],
	[2, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2, 2, 2, 2],
	[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 2, 2, 2, 2, 2, 2],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
	[1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
]

const BOSS_MAP: Array = [
	[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
	[5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5, 5],
	[5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5],
	[5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5],
	[5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
	[5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
	[5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
	[5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
	[5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
	[5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
	[5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
	[5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
	[5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
	[5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
	[5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5],
	[5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5],
	[5, 5, 5, 5, 4, 4, 4, 4, 4, 4, 4, 4, 4, 5, 5, 5, 5],
	[5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5],
	[5, 5, 5, 5, 5, 5, 4, 4, 4, 4, 4, 5, 5, 5, 5, 5, 5],
]


static func rand_step(rng: RandomNumberGenerator, limit: int, step: int = 1) -> int:
	var val := rng.randi_range(0, maxi(0, limit - 1))
	return int(floor(float(val) / float(step))) * step


static func exp_to_next_level(lv: int, current_exp: int) -> int:
	if lv < 0 or lv >= NEXT_LEVEL_EXP.size():
		return 0
	return maxi(0, NEXT_LEVEL_EXP[lv] - current_exp)


static func apply_exp(lv: int, current_exp: int, gain: int) -> Dictionary:
	var new_exp := current_exp + gain
	var new_lv := lv
	var levels_gained := 0
	while new_lv < NEXT_LEVEL_EXP.size() and new_exp >= NEXT_LEVEL_EXP[new_lv]:
		new_lv += 1
		levels_gained += 1
	return {
		"lv": new_lv,
		"exp": new_exp,
		"levels_gained": levels_gained,
	}


static func compute_warp_position(pos: Vector2, player_width: float) -> Vector2:
	var new_y := pos.y + 40.0
	var new_x := pos.x + 80.0
	if new_x > float(GAME_WIDTH) - player_width:
		new_x -= 160.0
	return Vector2(new_x, new_y)


static func thunder_scale_for_level(lv: int) -> float:
	return clampf(float(lv) / 5.0, 0.6, 1.0)


static func boss_crystal_position(index: int, total_hp: int, boss_center: Vector2) -> Vector2:
	var angle := (0.25 - (float(index) * (1.5 / float(maxi(1, total_hp - 1))))) * PI
	return Vector2(
		roundf(cos(angle) * 80.0 + boss_center.x),
		roundf(sin(angle) * 80.0 + boss_center.y)
	)
