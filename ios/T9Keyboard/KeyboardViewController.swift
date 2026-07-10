import UIKit

/// System keyboard extension entry point — old Nokia-style multi-tap T9.
@objc(KeyboardViewController)
final class KeyboardViewController: UIInputViewController {
    private var engine: T9MultiTapEngine!
    private var padView: T9PadView!
    private let modeLabel = UILabel()
    private let pendingLabel = UILabel()
    private var heightConstraint: NSLayoutConstraint?

    override func viewDidLoad() {
        super.viewDidLoad()
        view.backgroundColor = UIColor(white: 0.12, alpha: 1)

        engine = T9MultiTapEngine(
            onInsert: { [weak self] text in
                self?.textDocumentProxy.insertText(text)
                self?.playClick()
            },
            onDeleteBackward: { [weak self] in
                self?.textDocumentProxy.deleteBackward()
                self?.playClick()
            },
            onStateChange: { [weak self] in
                self?.padView?.refreshChrome()
            }
        )

        buildChrome()
        buildPad()
        buildToolbar()
    }

    override func viewWillAppear(_ animated: Bool) {
        super.viewWillAppear(animated)
        // Custom keyboards must request a concrete height; otherwise the system
        // may collapse the input view.
        if heightConstraint == nil {
            let constraint = view.heightAnchor.constraint(equalToConstant: 280)
            constraint.priority = .defaultHigh
            constraint.isActive = true
            heightConstraint = constraint
        }
    }

    // MARK: - UI

    private func buildChrome() {
        modeLabel.translatesAutoresizingMaskIntoConstraints = false
        modeLabel.font = .monospacedSystemFont(ofSize: 13, weight: .semibold)
        modeLabel.textColor = UIColor(white: 0.85, alpha: 1)
        modeLabel.text = "abc"

        pendingLabel.translatesAutoresizingMaskIntoConstraints = false
        pendingLabel.font = .systemFont(ofSize: 20, weight: .bold)
        pendingLabel.textColor = .systemYellow
        pendingLabel.textAlignment = .center
        pendingLabel.text = " "
        pendingLabel.accessibilityIdentifier = "t9-pending"
    }

    private func buildPad() {
        padView = T9PadView(engine: engine)
        padView.onShiftModeChange = { [weak self] mode in
            self?.modeLabel.text = mode.label
        }
        padView.onPendingChange = { [weak self] pending in
            self?.pendingLabel.text = pending.isEmpty ? " " : pending
        }
        view.addSubview(padView)
    }

    private func buildToolbar() {
        let nextKeyboard = UIButton(type: .system)
        nextKeyboard.translatesAutoresizingMaskIntoConstraints = false
        nextKeyboard.setImage(
            UIImage(systemName: "globe"),
            for: .normal
        )
        nextKeyboard.tintColor = .white
        nextKeyboard.accessibilityLabel = "Next keyboard"
        nextKeyboard.addTarget(
            self,
            action: #selector(handleInputModeList(from:with:)),
            for: .allTouchEvents
        )

        let deleteButton = UIButton(type: .system)
        deleteButton.translatesAutoresizingMaskIntoConstraints = false
        deleteButton.setImage(UIImage(systemName: "delete.left"), for: .normal)
        deleteButton.tintColor = .white
        deleteButton.accessibilityIdentifier = "t9-delete"
        deleteButton.addAction(UIAction { [weak self] _ in
            self?.engine.deleteBackward()
            self?.padView.refreshChrome()
        }, for: .touchUpInside)

        let returnButton = UIButton(type: .system)
        returnButton.translatesAutoresizingMaskIntoConstraints = false
        var returnConfig = UIButton.Configuration.filled()
        returnConfig.baseBackgroundColor = UIColor.systemBlue
        returnConfig.baseForegroundColor = .white
        returnConfig.title = "return"
        returnConfig.cornerStyle = .medium
        returnButton.configuration = returnConfig
        returnButton.accessibilityIdentifier = "t9-return"
        returnButton.addAction(UIAction { [weak self] _ in
            self?.engine.commitPending()
            self?.textDocumentProxy.insertText("\n")
            self?.playClick()
            self?.padView.refreshChrome()
        }, for: .touchUpInside)

        let toolbar = UIStackView(arrangedSubviews: [
            nextKeyboard, modeLabel, pendingLabel, deleteButton, returnButton,
        ])
        toolbar.axis = .horizontal
        toolbar.alignment = .center
        toolbar.spacing = 12
        toolbar.translatesAutoresizingMaskIntoConstraints = false
        view.addSubview(toolbar)

        NSLayoutConstraint.activate([
            toolbar.topAnchor.constraint(equalTo: view.topAnchor, constant: 6),
            toolbar.leadingAnchor.constraint(equalTo: view.leadingAnchor, constant: 12),
            toolbar.trailingAnchor.constraint(equalTo: view.trailingAnchor, constant: -12),
            toolbar.heightAnchor.constraint(equalToConstant: 36),

            nextKeyboard.widthAnchor.constraint(equalToConstant: 36),
            deleteButton.widthAnchor.constraint(equalToConstant: 36),
            returnButton.widthAnchor.constraint(greaterThanOrEqualToConstant: 72),
            pendingLabel.widthAnchor.constraint(greaterThanOrEqualToConstant: 28),

            padView.topAnchor.constraint(equalTo: toolbar.bottomAnchor, constant: 4),
            padView.leadingAnchor.constraint(equalTo: view.leadingAnchor),
            padView.trailingAnchor.constraint(equalTo: view.trailingAnchor),
            padView.bottomAnchor.constraint(equalTo: view.bottomAnchor),
        ])
    }

    private func playClick() {
        // Honored when Settings → Sounds → Keyboard Clicks is on, and only
        // because this controller conforms to UIInputViewAudioFeedback.
        UIDevice.current.playInputClick()
    }
}

extension KeyboardViewController: UIInputViewAudioFeedback {
    var enableInputClicksWhenVisible: Bool { true }
}
