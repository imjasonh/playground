## Score / timer HUD plus on-screen crane controls for touch.
extends CanvasLayer

@onready var score_label: Label = $Root/TopBar/Score
@onready var time_label: Label = $Root/TopBar/Time
@onready var status_label: Label = $Root/Status
@onready var end_panel: PanelContainer = $Root/EndPanel
@onready var end_label: Label = $Root/EndPanel/Margin/VBox/EndText
@onready var help_label: Label = $Root/Help

var _game: Node3D
var _crane: Crane

# Touch button state
var _held_actions: Dictionary = {}


func _ready() -> void:
	_game = get_parent()
	await get_tree().process_frame
	_crane = _game.get_node_or_null("Crane") as Crane
	if _game.has_signal("score_changed"):
		_game.score_changed.connect(_on_score)
		_game.time_changed.connect(_on_time)
		_game.status_changed.connect(_on_status)
		_game.game_ended.connect(_on_ended)
	end_panel.visible = false
	_wire_touch_buttons()


func _process(_delta: float) -> void:
	if _crane == null:
		return
	var rotate := 0.0
	var trolley := 0.0
	var hook := 0.0
	if _held_actions.get("rot_left", false):
		rotate -= 1.0
	if _held_actions.get("rot_right", false):
		rotate += 1.0
	if _held_actions.get("boom_in", false):
		trolley -= 1.0
	if _held_actions.get("boom_out", false):
		trolley += 1.0
	if _held_actions.get("hook_up", false):
		hook -= 1.0
	if _held_actions.get("hook_down", false):
		hook += 1.0
	_crane.set_touch_axis(rotate, trolley, hook)


func _on_score(score: int) -> void:
	score_label.text = "SCORE  %d" % score


func _on_time(seconds: float) -> void:
	var m := int(seconds) / 60
	var s := int(seconds) % 60
	time_label.text = "%d:%02d" % [m, s]
	if seconds < 30.0:
		time_label.add_theme_color_override("font_color", Color(0.95, 0.45, 0.3))
	else:
		time_label.add_theme_color_override("font_color", Color(0.92, 0.93, 0.9))


func _on_status(text: String) -> void:
	status_label.text = text


func _on_ended(final_score: int, delivered: int) -> void:
	end_panel.visible = true
	end_label.text = "Shift complete\n%d points · %d loads\n\nSpace / Grab to go again" % [final_score, delivered]


func _wire_touch_buttons() -> void:
	_bind_hold($Root/Controls/LeftCol/RotLeft, "rot_left")
	_bind_hold($Root/Controls/LeftCol/RotRight, "rot_right")
	_bind_hold($Root/Controls/LeftCol/BoomIn, "boom_in")
	_bind_hold($Root/Controls/LeftCol/BoomOut, "boom_out")
	_bind_hold($Root/Controls/RightCol/HookUp, "hook_up")
	_bind_hold($Root/Controls/RightCol/HookDown, "hook_down")
	var grab_btn: BaseButton = $Root/Controls/RightCol/Grab
	grab_btn.pressed.connect(func() -> void:
		if _crane:
			_crane.request_grab_toggle()
	)


func _bind_hold(button: BaseButton, action: String) -> void:
	button.button_down.connect(func() -> void:
		_held_actions[action] = true
	)
	button.button_up.connect(func() -> void:
		_held_actions[action] = false
	)
	button.mouse_exited.connect(func() -> void:
		_held_actions[action] = false
	)
