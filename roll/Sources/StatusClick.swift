enum StatusClick: Equatable, Sendable {
    case roll
    case menu

    init(rightMouse: Bool, control: Bool) {
        if rightMouse || control {
            self = .menu
        } else {
            self = .roll
        }
    }
}
