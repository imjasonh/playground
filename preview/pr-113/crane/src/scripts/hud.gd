## Elapsed-time HUD plus on-screen crane controls for touch.
extends CanvasLayer

@onready var progress_label: Label = $Root/TopBar/Score
@onready var time_label: Label = $Root/TopBar/Time
@onready var status_label: Label = $Root/Status
@onready var end_panel: PanelContainer = $Root/EndPanel
@onready var end_label: Label = $Root/EndPanel/Margin/VBox/EndText
@onready var help_label: Label = $Root/Help

var _game: Node3D
var _crane: Crane
var _held_actions: Dictionary = {}


func _ready() -> void:
	_game = get_parent()
	await get_tree().process_frame
	_crane = _game.get_node_or_null("Crane") as Crane
	if _game.has_signal("progress_changed"):
		_game.progress_changed.connect(_on_progress)
		_game.time_changed.connect(_on_time)
		_game.status_changed.connect(_on_status)
		_game.game_ended.connect(_on_ended)
	end_panel.visible = false
	if help_label:
		help_label.text = "A/D slew · W/S trolley · Q/E hoist · Space grab   ·   Deliver all 3 crates — clock is running"
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


func _on_progress(delivered: int, total: int) -> void:
	progress_label.text = "CRATES  %d / %d" % [delivered, total]


func _on_time(seconds: float) -> void:
	time_label.text = _format_time(seconds)
	time_label.add_theme_color_override("font_color", Color(0.92, 0.93, 0.9))


func _on_status(text: String) -> void:
	status_label.text = text


func _on_ended(elapsed_seconds: float, soft_count: int) -> void:
	end_panel.visible = true
	var soft_line := ""
	if soft_count > 0:
		soft_line = "\n%d soft set%s" % [soft_count, "s" if soft_count != 1 else ""]
	end_label.text = "Yard clear\n%s%s\n\nSpace / Grab to go again" % [_format_time(elapsed_seconds), soft_line]


func _format_time(seconds: float) -> String:
	var total := int(floor(seconds))
	var m := total / 60
	var s := total % 60
	var tenths := int(floor((seconds - float(total)) * 10.0))
	return "%d:%02d.%d" % [m, s, tenths]


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
