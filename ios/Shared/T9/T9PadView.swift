import UIKit

/// Classic 12-key multi-tap pad. Drives a ``T9MultiTapEngine`` and reports
/// chrome updates (shift mode + pending letter preview) to the host.
final class T9PadView: UIView {
    var onShiftModeChange: ((T9ShiftMode) -> Void)?
    var onPendingChange: ((String) -> Void)?

    private let engine: T9MultiTapEngine
    private let grid = UIStackView()
    private var keyButtons: [T9PadKey: UIButton] = [:]
    /// Tags whose long-press already fired — suppress the following touch-up tap.
    private var longPressConsumedTags: Set<Int> = []

    init(engine: T9MultiTapEngine) {
        self.engine = engine
        super.init(frame: .zero)
        translatesAutoresizingMaskIntoConstraints = false
        backgroundColor = UIColor(white: 0.12, alpha: 1)
        buildGrid()
    }

    @available(*, unavailable)
    required init?(coder: NSCoder) {
        fatalError("init(coder:) has not been implemented")
    }

    func refreshChrome() {
        onShiftModeChange?(engine.shiftMode)
        onPendingChange?(engine.pendingPreview)
        // Reflect shift mode on the * key subtitle.
        if let star = keyButtons[.star] {
            star.configuration = Self.makeConfiguration(
                title: "*",
                subtitle: engine.shiftMode.label,
                emphasized: true
            )
        }
    }

    // MARK: - Layout

    private func buildGrid() {
        grid.axis = .vertical
        grid.spacing = 6
        grid.distribution = .fillEqually
        grid.translatesAutoresizingMaskIntoConstraints = false
        addSubview(grid)

        NSLayoutConstraint.activate([
            grid.topAnchor.constraint(equalTo: topAnchor, constant: 8),
            grid.leadingAnchor.constraint(equalTo: leadingAnchor, constant: 8),
            grid.trailingAnchor.constraint(equalTo: trailingAnchor, constant: -8),
            grid.bottomAnchor.constraint(equalTo: bottomAnchor, constant: -8),
        ])

        for row in T9PadLayout.rows {
            let rowStack = UIStackView()
            rowStack.axis = .horizontal
            rowStack.spacing = 6
            rowStack.distribution = .fillEqually
            for key in row {
                let button = makeKeyButton(for: key)
                keyButtons[key] = button
                rowStack.addArrangedSubview(button)
            }
            grid.addArrangedSubview(rowStack)
        }

        refreshChrome()
    }

    private func makeKeyButton(for key: T9PadKey) -> UIButton {
        let button = UIButton(type: .system)
        button.configuration = Self.makeConfiguration(
            title: key.title,
            subtitle: key.subtitle,
            emphasized: key == .star || key == .hash
        )
        button.accessibilityIdentifier = "t9-key-\(key.title)"
        button.addAction(UIAction { [weak self] _ in
            guard let self else { return }
            if self.longPressConsumedTags.remove(button.tag) != nil {
                return
            }
            self.engine.tap(key)
            self.refreshChrome()
        }, for: .touchUpInside)

        let longPress = UILongPressGestureRecognizer(
            target: self,
            action: #selector(handleLongPress(_:))
        )
        longPress.minimumPressDuration = 0.45
        button.addGestureRecognizer(longPress)
        button.tag = Self.tag(for: key)
        return button
    }

    @objc private func handleLongPress(_ gesture: UILongPressGestureRecognizer) {
        guard gesture.state == .began,
              let button = gesture.view as? UIButton,
              let key = Self.key(forTag: button.tag)
        else { return }
        longPressConsumedTags.insert(button.tag)
        UIDevice.current.playInputClick()
        engine.longPress(key)
        refreshChrome()
    }

    private static func makeConfiguration(
        title: String,
        subtitle: String,
        emphasized: Bool
    ) -> UIButton.Configuration {
        var config = UIButton.Configuration.filled()
        config.baseBackgroundColor = emphasized
            ? UIColor(white: 0.22, alpha: 1)
            : UIColor(white: 0.28, alpha: 1)
        config.baseForegroundColor = .white
        config.cornerStyle = .medium
        config.titleAlignment = .center
        config.title = title
        config.subtitle = subtitle
        config.titleTextAttributesTransformer = UIConfigurationTextAttributesTransformer { incoming in
            var outgoing = incoming
            outgoing.font = UIFont.systemFont(ofSize: 22, weight: .semibold)
            outgoing.foregroundColor = .white
            return outgoing
        }
        config.subtitleTextAttributesTransformer = UIConfigurationTextAttributesTransformer { incoming in
            var outgoing = incoming
            outgoing.font = UIFont.systemFont(ofSize: 11, weight: .medium)
            outgoing.foregroundColor = UIColor(white: 0.75, alpha: 1)
            return outgoing
        }
        return config
    }

    private static func tag(for key: T9PadKey) -> Int {
        switch key {
        case .digit(let n): return n
        case .star: return 10
        case .hash: return 11
        }
    }

    private static func key(forTag tag: Int) -> T9PadKey? {
        switch tag {
        case 0...9: return .digit(tag)
        case 10: return .star
        case 11: return .hash
        default: return nil
        }
    }
}
