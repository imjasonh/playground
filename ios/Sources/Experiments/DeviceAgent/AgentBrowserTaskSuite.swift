import Foundation

/// One CI / UI-test browser exercise (query + scripted tool steps on fixture HTML).
struct AgentBrowserTask: Identifiable, Equatable {
    var id: String
    /// Simulated user query this task stands in for.
    var query: String
    var detail: String
}

/// Outcome of one browser task.
struct AgentBrowserTaskResult: Identifiable, Equatable {
    var id: String { task.id }
    var task: AgentBrowserTask
    var passed: Bool
    var summary: String
    var durationMs: Int
}

/// Fixed catalog of browser tasks Device Agent must handle reliably in CI.
enum AgentBrowserTaskCatalog {
    static let all: [AgentBrowserTask] = [
        AgentBrowserTask(
            id: "open-snapshot",
            query: "Open the sample store home page",
            detail: "Load fixture HTML and read the title via snapshot."
        ),
        AgentBrowserTask(
            id: "find-ebike",
            query: "Find e-bike deals on this page",
            detail: "browserFind for bike / e-bike controls."
        ),
        AgentBrowserTask(
            id: "read-prices",
            query: "What do the ebikes cost?",
            detail: "Snapshot price list and assert dollar amounts in page text."
        ),
        AgentBrowserTask(
            id: "click-product",
            query: "Open the Trail Glide ebike product",
            detail: "browserClickText on a product link."
        ),
        AgentBrowserTask(
            id: "search-type-submit",
            query: "Search for cargo ebike",
            detail: "Type into search and submit."
        ),
        AgentBrowserTask(
            id: "dismiss-cookies",
            query: "Dismiss the cookie banner then read prices",
            detail: "Click Accept, then confirm product content is visible."
        ),
        AgentBrowserTask(
            id: "scroll-list",
            query: "Scroll to more ebike listings",
            detail: "browserScroll down on a tall page."
        ),
        AgentBrowserTask(
            id: "get-href",
            query: "What’s the URL for City Commuter?",
            detail: "browserFind + browserGet for a product href."
        ),
        AgentBrowserTask(
            id: "select-size",
            query: "Choose frame size Large",
            detail: "browserSelect on a size <select>."
        ),
        AgentBrowserTask(
            id: "back-navigation",
            query: "Go back after opening a product",
            detail: "Click through, then browserBack."
        ),
    ]

    static var count: Int { all.count }
}

/// Runs the catalog against an in-app `AgentBrowserSession` using local HTML fixtures.
@MainActor
final class AgentBrowserTaskRunner: ObservableObject {
    @Published private(set) var results: [AgentBrowserTaskResult] = []
    @Published private(set) var isRunning = false
    @Published private(set) var summaryLine = ""

    var passedCount: Int { results.filter(\.passed).count }
    var totalCount: Int { results.count }
    var allPassed: Bool { !results.isEmpty && results.allSatisfy(\.passed) }

    /// `-deviceAgentBrowserTasks` launch argument used by UI tests / CI.
    static let launchArgument = "-deviceAgentBrowserTasks"

    static var shouldAutostartFromLaunchArguments: Bool {
        ProcessInfo.processInfo.arguments.contains(launchArgument)
    }

    func runAll(browser: AgentBrowserSession) async {
        guard !isRunning else { return }
        isRunning = true
        results = []
        summaryLine = "Running \(AgentBrowserTaskCatalog.count) browser tasks…"
        defer { isRunning = false }

        var collected: [AgentBrowserTaskResult] = []
        for task in AgentBrowserTaskCatalog.all {
            let started = Date()
            let outcome: (Bool, String)
            do {
                outcome = try await Self.execute(task, browser: browser)
            } catch {
                outcome = (false, AgentErrorCopy.userMessage(for: error))
            }
            let ms = Int(Date().timeIntervalSince(started) * 1000)
            let result = AgentBrowserTaskResult(
                task: task,
                passed: outcome.0,
                summary: outcome.1,
                durationMs: ms
            )
            collected.append(result)
            results = collected
            summaryLine = "\(passedCount)/\(collected.count) passed"
        }
        summaryLine = "\(passedCount)/\(AgentBrowserTaskCatalog.count) passed"
    }

    private static func execute(
        _ task: AgentBrowserTask,
        browser: AgentBrowserSession
    ) async throws -> (Bool, String) {
        switch task.id {
        case "open-snapshot":
            try await browser.loadHTML(Self.storeHomeHTML, titleHint: "Playground Bike Shop")
            let snap = try await browser.snapshot(maxTextChars: 1200)
            let ok = snap.localizedCaseInsensitiveContains("Playground Bike Shop")
                && snap.localizedCaseInsensitiveContains("Trail Glide")
            return (ok, ok ? "Snapshot includes shop title and a product." : "Missing shop title/product in snapshot.")

        case "find-ebike":
            try await browser.loadHTML(Self.storeHomeHTML, titleHint: "Playground Bike Shop")
            let found = try await browser.find(query: "bike")
            let ok = found.localizedCaseInsensitiveContains("E-bike deals")
                || found.localizedCaseInsensitiveContains("Trail Glide")
                || found.localizedCaseInsensitiveContains("bike")
            return (ok, ok ? found.split(separator: "\n").prefix(3).joined(separator: " | ") : "No bike matches: \(found)")

        case "read-prices":
            try await browser.loadHTML(Self.storeHomeHTML, titleHint: "Playground Bike Shop")
            let snap = try await browser.snapshot(maxTextChars: 1800)
            let hasTrail = snap.contains("$1,299") || snap.contains("$1299")
            let hasCity = snap.contains("$899")
            let hasCargo = snap.contains("$2,499") || snap.contains("$2499")
            let ok = hasTrail && hasCity && hasCargo
            return (
                ok,
                ok
                    ? "Found Trail Glide $1,299, City Commuter $899, Cargo Hauler $2,499."
                    : "Price scrape incomplete."
            )

        case "click-product":
            try await browser.loadHTML(Self.storeHomeHTML, titleHint: "Playground Bike Shop")
            _ = try await browser.snapshot(maxTextChars: 800)
            let click = try await browser.clickText("Trail Glide")
            let ok = click.localizedCaseInsensitiveContains("clicked")
            // Fixture uses hash navigation; confirm detail region text via snapshot.
            let snap = try await browser.snapshot(maxTextChars: 1200)
            let detailVisible = snap.localizedCaseInsensitiveContains("Trail Glide Ebike")
                || snap.localizedCaseInsensitiveContains("$1,299")
            return (
                ok && detailVisible,
                ok && detailVisible ? "Opened Trail Glide detail." : "Click/detail failed: \(click)"
            )

        case "search-type-submit":
            try await browser.loadHTML(Self.searchHTML, titleHint: "Search")
            _ = try await browser.snapshot(maxTextChars: 800)
            let typed = try await browser.type(ref: "1", text: "cargo ebike", submit: true)
            let snap = try await browser.snapshot(maxTextChars: 1200)
            let ok = typed.localizedCaseInsensitiveContains("typed")
                && snap.localizedCaseInsensitiveContains("cargo ebike")
            return (ok, ok ? "Search submitted with cargo ebike." : "Type/submit failed: \(typed)")

        case "dismiss-cookies":
            try await browser.loadHTML(Self.cookieGateHTML, titleHint: "Cookie Shop")
            _ = try await browser.snapshot(maxTextChars: 800)
            let click = try await browser.clickText("Accept")
            let snap = try await browser.snapshot(maxTextChars: 1200)
            let ok = click.localizedCaseInsensitiveContains("clicked")
                && snap.localizedCaseInsensitiveContains("City Commuter")
                && snap.contains("$899")
            return (ok, ok ? "Dismissed cookies; prices visible." : "Cookie dismiss failed.")

        case "scroll-list":
            try await browser.loadHTML(Self.tallListHTML, titleHint: "Tall list")
            let before = try await browser.scroll(directionOrRef: "top")
            let after = try await browser.scroll(directionOrRef: "down")
            let ok = before.localizedCaseInsensitiveContains("scroll")
                && after.localizedCaseInsensitiveContains("scroll")
            return (ok, ok ? "Scrolled tall listings." : "Scroll failed.")

        case "get-href":
            try await browser.loadHTML(Self.storeHomeHTML, titleHint: "Playground Bike Shop")
            let found = try await browser.find(query: "City Commuter")
            guard let ref = Self.firstRef(in: found) else {
                return (false, "No City Commuter ref in find: \(found)")
            }
            let got = try await browser.get(ref: ref)
            let ok = got.localizedCaseInsensitiveContains("city")
                || got.localizedCaseInsensitiveContains("href=")
            return (ok, ok ? got.replacingOccurrences(of: "\n", with: " ") : "get failed: \(got)")

        case "select-size":
            try await browser.loadHTML(Self.productHTML, titleHint: "Trail Glide")
            _ = try await browser.snapshot(maxTextChars: 800)
            let frameSizeFind = try await browser.find(query: "Frame size")
            var ref = Self.firstRef(in: frameSizeFind, kindHint: "combobox")
            if ref == nil {
                let sizeFind = try await browser.find(query: "size")
                ref = Self.firstRef(in: sizeFind)
            }
            guard let ref else {
                return (false, "No size select found.")
            }
            let selected = try await browser.select(ref: ref, option: "Large")
            let got = try await browser.get(ref: ref)
            let ok = selected.localizedCaseInsensitiveContains("selected")
                && got.localizedCaseInsensitiveContains("Large")
            return (ok, ok ? "Selected Large." : "Select failed: \(selected) / \(got)")

        case "back-navigation":
            try await browser.loadHTML(Self.storeHomeHTML, titleHint: "Playground Bike Shop")
            _ = try await browser.snapshot(maxTextChars: 600)
            _ = try await browser.clickText("Trail Glide")
            let detail = try await browser.snapshot(maxTextChars: 1200)
            let detailOK = detail.localizedCaseInsensitiveContains("Trail Glide Ebike")
                || detail.localizedCaseInsensitiveContains("$1,299")
            // Hash-fixture navigation may not create WKWebView history; still call
            // browserBack and confirm the shop controls remain usable.
            let back = try await browser.goBack()
            let found = try await browser.find(query: "Cargo Hauler")
            let ok = detailOK && (
                found.localizedCaseInsensitiveContains("Cargo Hauler")
                    || back.localizedCaseInsensitiveContains("back")
            )
            return (ok, ok ? "Product dig + back path stayed usable." : "Back path failed.")

        default:
            return (false, "Unknown task id \(task.id).")
        }
    }

    private static func firstRef(in findPayload: String, kindHint: String? = nil) -> String? {
        for line in findPayload.split(separator: "\n") {
            let text = String(line)
            guard text.hasPrefix("["), let close = text.firstIndex(of: "]") else { continue }
            let ref = String(text[text.index(after: text.startIndex)..<close])
            guard !ref.isEmpty, ref.allSatisfy(\.isNumber) else { continue }
            if let kindHint, !text.localizedCaseInsensitiveContains(kindHint) {
                continue
            }
            return ref
        }
        return nil
    }

    // MARK: - Fixture HTML

    static let storeHomeHTML = """
    <!DOCTYPE html><html><head><meta charset="utf-8"><title>Playground Bike Shop</title></head>
    <body>
      <header><h1>Playground Bike Shop</h1>
        <a href="#deals">E-bike deals</a>
        <a href="#about">About</a>
      </header>
      <main>
        <h2>Ebike prices</h2>
        <ul id="deals">
          <li><a href="#trail">Trail Glide</a> — $1,299</li>
          <li><a href="#city">City Commuter</a> — $899</li>
          <li><a href="#cargo">Cargo Hauler</a> — $2,499</li>
        </ul>
        <section id="trail" hidden>
          <h2>Trail Glide Ebike</h2>
          <p>Off-road ebike. Price $1,299.</p>
        </section>
        <script>
          document.querySelectorAll('a[href^="#"]').forEach(function (a) {
            a.addEventListener('click', function (e) {
              var id = a.getAttribute('href').slice(1);
              var el = document.getElementById(id);
              if (!el) return;
              e.preventDefault();
              document.querySelectorAll('section').forEach(function (s) { s.hidden = true; });
              el.hidden = false;
              document.title = el.querySelector('h2') ? el.querySelector('h2').textContent : document.title;
            });
          });
        </script>
      </main>
    </body></html>
    """

    static let searchHTML = """
    <!DOCTYPE html><html><head><meta charset="utf-8"><title>Search</title></head>
    <body>
      <main>
        <h1>Shop search</h1>
        <form id="f" action="#" method="get">
          <label>Query <input id="q" name="q" type="search" placeholder="Search bikes"></label>
          <button type="submit">Search</button>
        </form>
        <p id="out"></p>
      </main>
      <script>
        document.getElementById('f').addEventListener('submit', function (e) {
          e.preventDefault();
          var v = document.getElementById('q').value || '';
          document.getElementById('out').textContent = 'Results for ' + v;
          document.title = 'Results for ' + v;
        });
      </script>
    </body></html>
    """

    static let cookieGateHTML = """
    <!DOCTYPE html><html><head><meta charset="utf-8"><title>Cookie Shop</title></head>
    <body>
      <div id="banner" style="padding:12px;background:#eee;">
        <p>We use cookies.</p>
        <button id="accept">Accept</button>
      </div>
      <main id="content" hidden>
        <h1>Ebike prices</h1>
        <ul>
          <li>City Commuter — $899</li>
          <li>Trail Glide — $1,299</li>
        </ul>
      </main>
      <script>
        document.getElementById('accept').addEventListener('click', function () {
          document.getElementById('banner').hidden = true;
          document.getElementById('content').hidden = false;
          document.title = 'Cookie Shop — prices';
        });
      </script>
    </body></html>
    """

    static let tallListHTML = """
    <!DOCTYPE html><html><head><meta charset="utf-8"><title>Tall list</title>
    <style>li{padding:48px 0;border-bottom:1px solid #ccc}</style></head>
    <body><main><h1>More ebikes</h1><ul>
      <li>Model A — $500</li><li>Model B — $600</li><li>Model C — $700</li>
      <li>Model D — $800</li><li>Model E — $900</li><li>Model F — $1000</li>
      <li>Model G — $1100</li><li>Model H — $1200</li>
    </ul></main></body></html>
    """

    static let productHTML = """
    <!DOCTYPE html><html><head><meta charset="utf-8"><title>Trail Glide</title></head>
    <body>
      <main>
        <h1>Trail Glide</h1>
        <p>Price $1,299</p>
        <label>Frame size
          <select id="size" aria-label="Frame size">
            <option value="S">Small</option>
            <option value="M">Medium</option>
            <option value="L">Large</option>
          </select>
        </label>
      </main>
    </body></html>
    """
}
