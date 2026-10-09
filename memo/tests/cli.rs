//! End-to-end tests: run the memo binary on real commands and check when it
//! replays and when it runs again.

use std::fs;
use std::io::Write;
use std::net::TcpListener;
use std::path::{Path, PathBuf};
use std::process::{Command, Output, Stdio};
use std::time::{Duration, Instant};

struct Sandbox {
    dir: tempfile::TempDir,
    cache: PathBuf,
}

impl Sandbox {
    fn new() -> Sandbox {
        let dir = tempfile::tempdir().unwrap();
        let cache = dir.path().join(".memo-cache");
        Sandbox { dir, cache }
    }

    fn path(&self, p: &str) -> PathBuf {
        self.dir.path().join(p)
    }

    fn write(&self, p: &str, data: &str) {
        fs::write(self.path(p), data).unwrap();
    }

    fn cmd(&self, args: &[&str]) -> Command {
        let mut c = Command::new(env!("CARGO_BIN_EXE_memo"));
        c.env("MEMO_CACHE_DIR", &self.cache)
            .current_dir(self.dir.path())
            .stdin(Stdio::null());
        c.args(args);
        c
    }

    /// Runs `memo -v ARGS` with standard input closed.
    fn memo(&self, args: &[&str]) -> Run {
        let mut all = vec!["-v"];
        all.extend_from_slice(args);
        Run(self.cmd(&all).output().unwrap())
    }
}

struct Run(Output);

impl Run {
    fn stdout(&self) -> String {
        String::from_utf8_lossy(&self.0.stdout).into_owned()
    }

    fn stderr(&self) -> String {
        String::from_utf8_lossy(&self.0.stderr).into_owned()
    }

    fn code(&self) -> i32 {
        self.0.status.code().unwrap_or(-1)
    }

    #[track_caller]
    fn ran(&self) -> &Run {
        assert!(
            self.stderr().contains("memo: running"),
            "expected a run:\n{}",
            self.stderr()
        );
        self
    }

    #[track_caller]
    fn replayed(&self) -> &Run {
        assert!(
            self.stderr().contains("memo: replaying"),
            "expected a replay:\n{}",
            self.stderr()
        );
        self
    }

    #[track_caller]
    fn cached(&self) -> &Run {
        assert!(
            self.stderr().contains("memo: cached the result"),
            "expected the result to be cached:\n{}",
            self.stderr()
        );
        self
    }

    #[track_caller]
    fn not_cached(&self, why: &str) -> &Run {
        let err = self.stderr();
        assert!(
            err.contains("memo: not cached") && err.contains(why),
            "expected 'not cached: ...{why}...':\n{err}"
        );
        self
    }
}

#[test]
fn replays_until_an_input_changes() {
    let s = Sandbox::new();
    s.write("a.txt", "one\n");
    let first = s.memo(&["cat", "a.txt"]);
    first.ran().cached();
    assert_eq!(first.stdout(), "one\n");
    let second = s.memo(&["cat", "a.txt"]);
    second.replayed();
    assert_eq!(second.stdout(), "one\n");
    s.write("a.txt", "two\n");
    let third = s.memo(&["cat", "a.txt"]);
    third.ran();
    assert!(
        third.stderr().contains("a.txt: content changed"),
        "{}",
        third.stderr()
    );
    assert_eq!(third.stdout(), "two\n");
}

#[test]
fn a_missing_file_that_appears_is_a_change() {
    let s = Sandbox::new();
    let script = "cat maybe.txt 2>/dev/null || echo none";
    assert_eq!(
        s.memo(&["sh", "-c", script]).ran().cached().stdout(),
        "none\n"
    );
    s.memo(&["sh", "-c", script]).replayed();
    s.write("maybe.txt", "here\n");
    let r = s.memo(&["sh", "-c", script]);
    r.ran();
    assert_eq!(r.stdout(), "here\n");
}

#[test]
fn new_directory_entries_are_a_change() {
    let s = Sandbox::new();
    fs::create_dir(s.path("d")).unwrap();
    s.write("d/one", "");
    assert_eq!(s.memo(&["ls", "d"]).ran().cached().stdout(), "one\n");
    s.memo(&["ls", "d"]).replayed();
    s.write("d/two", "");
    assert_eq!(s.memo(&["ls", "d"]).ran().stdout(), "one\ntwo\n");
}

#[test]
fn outputs_must_still_be_in_place() {
    let s = Sandbox::new();
    s.write("in.txt", "abc\n");
    let script = "tr a-z A-Z < in.txt > out.txt";
    s.memo(&["sh", "-c", script]).ran().cached();
    s.memo(&["sh", "-c", script]).replayed();
    fs::remove_file(s.path("out.txt")).unwrap();
    s.memo(&["sh", "-c", script]).ran();
    assert_eq!(fs::read_to_string(s.path("out.txt")).unwrap(), "ABC\n");
    s.write("out.txt", "edited\n");
    s.memo(&["sh", "-c", script]).ran();
    assert_eq!(fs::read_to_string(s.path("out.txt")).unwrap(), "ABC\n");
}

#[test]
fn changing_what_it_read_is_not_cached() {
    let s = Sandbox::new();
    let script = "echo line >> log.txt; wc -l < log.txt";
    s.memo(&["sh", "-c", script])
        .ran()
        .not_cached("changed it after reading it");
    let again = s.memo(&["sh", "-c", script]);
    again.ran();
    assert_eq!(again.stdout().trim(), "2");
}

#[test]
fn failures_are_cached_only_on_request() {
    let s = Sandbox::new();
    let r = s.memo(&["sh", "-c", "echo bad; exit 3"]);
    r.ran().not_cached("exited with status 3");
    assert_eq!(r.code(), 3);
    s.memo(&["sh", "-c", "echo bad; exit 3"]).ran();
    s.memo(&["--cache-failures", "sh", "-c", "echo bad; exit 3"])
        .ran()
        .cached();
    let replay = s.memo(&["--cache-failures", "sh", "-c", "echo bad; exit 3"]);
    replay.replayed();
    assert_eq!((replay.code(), replay.stdout().as_str()), (3, "bad\n"));
    s.memo(&["sh", "-c", "echo bad; exit 3"]).ran();
}

#[test]
fn a_signal_death_is_not_cached() {
    let s = Sandbox::new();
    let r = s.memo(&["sh", "-c", "kill -TERM $$"]);
    r.ran().not_cached("killed by signal 15");
    assert_eq!(r.code(), 143);
}

#[test]
fn network_access_needs_a_ttl() {
    let s = Sandbox::new();
    let listener = TcpListener::bind("127.0.0.1:0").unwrap();
    let port = listener.local_addr().unwrap().port();
    std::thread::spawn(move || {
        for conn in listener.incoming() {
            drop(conn);
        }
    });
    let script = format!("echo hi > /dev/tcp/127.0.0.1/{port}");
    s.memo(&["bash", "-c", &script])
        .ran()
        .not_cached(&format!("connected to 127.0.0.1:{port}"));
    s.memo(&["--ttl", "1h", "bash", "-c", &script])
        .ran()
        .cached();
    s.memo(&["--ttl", "1h", "bash", "-c", &script]).replayed();
}

#[test]
fn reading_piped_stdin_is_not_cached() {
    let s = Sandbox::new();
    let run = |args: &[&str]| {
        let mut all = vec!["-v"];
        all.extend_from_slice(args);
        let mut child = s
            .cmd(&all)
            .stdin(Stdio::piped())
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .spawn()
            .unwrap();
        child.stdin.take().unwrap().write_all(b"piped\n").unwrap();
        Run(child.wait_with_output().unwrap())
    };
    let r = run(&["cat"]);
    r.ran().not_cached("read standard input");
    assert_eq!(r.stdout(), "piped\n");
    run(&["echo", "hi"]).ran().cached();
    run(&["echo", "hi"]).replayed();
}

#[test]
fn stdin_from_a_file_is_an_input() {
    let s = Sandbox::new();
    s.write("in.txt", "first\n");
    let run = || {
        let f = fs::File::open(s.path("in.txt")).unwrap();
        Run(s.cmd(&["-v", "cat"]).stdin(f).output().unwrap())
    };
    run().ran().cached();
    assert_eq!(run().replayed().stdout(), "first\n");
    s.write("in.txt", "second\n");
    assert_eq!(run().ran().stdout(), "second\n");
}

#[test]
fn the_environment_is_part_of_the_key() {
    let s = Sandbox::new();
    let run = |args: &[&str], value: &str| {
        let mut all = vec!["-v"];
        all.extend_from_slice(args);
        Run(s.cmd(&all).env("X_VALUE", value).output().unwrap())
    };
    let script = ["sh", "-c", "echo $X_VALUE"];
    run(&script, "1").ran().cached();
    run(&script, "1").replayed();
    assert_eq!(run(&script, "2").ran().stdout(), "2\n");
    let ignoring = ["--ignore-env", "X_VALUE", "sh", "-c", "echo $X_VALUE"];
    run(&ignoring, "3").ran().cached();
    assert_eq!(run(&ignoring, "4").replayed().stdout(), "3\n");
}

#[test]
fn an_earlier_path_entry_can_shadow_the_program() {
    let s = Sandbox::new();
    fs::create_dir(s.path("first")).unwrap();
    fs::create_dir(s.path("second")).unwrap();
    let tool = |dir: &str, word: &str| {
        let p = s.path(&format!("{dir}/tool"));
        fs::write(&p, format!("#!/bin/sh\necho {word}\n")).unwrap();
        let mut perm = fs::metadata(&p).unwrap().permissions();
        std::os::unix::fs::PermissionsExt::set_mode(&mut perm, 0o755);
        fs::set_permissions(&p, perm).unwrap();
    };
    tool("second", "second");
    let path = format!(
        "{}:{}:{}",
        s.path("first").display(),
        s.path("second").display(),
        std::env::var("PATH").unwrap()
    );
    let run = || Run(s.cmd(&["-v", "tool"]).env("PATH", &path).output().unwrap());
    assert_eq!(run().ran().cached().stdout(), "second\n");
    run().replayed();
    tool("first", "first");
    assert_eq!(run().ran().stdout(), "first\n");
}

#[test]
fn ignored_paths_dont_invalidate() {
    let s = Sandbox::new();
    fs::create_dir(s.path("scratch")).unwrap();
    s.write("scratch/note", "1");
    let args = ["--ignore", "scratch", "cat", "scratch/note"];
    s.memo(&args).ran().cached();
    s.write("scratch/note", "2");
    assert_eq!(s.memo(&args).replayed().stdout(), "1");
}

#[test]
fn background_processes_keep_running() {
    let s = Sandbox::new();
    s.write("a.txt", "from the background\n");
    let start = Instant::now();
    s.memo(&["sh", "-c", "(sleep 0.5; cat a.txt > bg.txt) & echo started"])
        .ran()
        .not_cached("background processes");
    assert!(
        start.elapsed() < Duration::from_secs(3),
        "memo waited for the background process"
    );
    let deadline = Instant::now() + Duration::from_secs(10);
    loop {
        if fs::read_to_string(s.path("bg.txt")).is_ok_and(|c| c == "from the background\n") {
            break;
        }
        assert!(
            Instant::now() < deadline,
            "the background process never finished its work"
        );
        std::thread::sleep(Duration::from_millis(50));
    }
}

#[test]
fn explain_reports_what_changed() {
    let s = Sandbox::new();
    s.write("a.txt", "one\n");
    s.memo(&["cat", "a.txt"]).ran().cached();
    let fresh = Run(s.cmd(&["explain", "cat", "a.txt"]).output().unwrap());
    assert_eq!(fresh.code(), 0, "{}", fresh.stdout());
    assert!(
        fresh.stdout().contains("would be replayed"),
        "{}",
        fresh.stdout()
    );
    s.write("a.txt", "two\n");
    let stale = Run(s.cmd(&["explain", "cat", "a.txt"]).output().unwrap());
    assert_eq!(stale.code(), 1);
    assert!(
        stale.stdout().contains("a.txt: content changed"),
        "{}",
        stale.stdout()
    );
}

#[test]
fn refresh_and_clear() {
    let s = Sandbox::new();
    s.memo(&["echo", "hi"]).ran().cached();
    s.memo(&["--refresh", "echo", "hi"]).cached();
    s.memo(&["echo", "hi"]).replayed();
    let cleared = Run(s.cmd(&["clear"]).output().unwrap());
    assert_eq!(cleared.code(), 0);
    s.memo(&["echo", "hi"]).ran();
}

#[test]
fn a_missing_command_exits_127() {
    let s = Sandbox::new();
    let r = s.memo(&["memo-test-no-such-command"]);
    assert_eq!(r.code(), 127, "{}", r.stderr());
}

#[test]
fn both_streams_are_replayed() {
    let s = Sandbox::new();
    let script = "echo out1; echo err1 >&2; echo out2";
    s.memo(&["sh", "-c", script]).ran().cached();
    let r = s.memo(&["sh", "-c", script]);
    r.replayed();
    assert_eq!(r.stdout(), "out1\nout2\n");
    assert!(r.stderr().contains("err1\n"), "{}", r.stderr());
}

#[test]
fn a_terminal_stays_a_terminal() {
    if Command::new("script").arg("--version").output().is_err() {
        eprintln!("skipping: util-linux script isn't installed");
        return;
    }
    let s = Sandbox::new();
    let memo = env!("CARGO_BIN_EXE_memo");
    let inner = format!("{memo} -- sh -c 'test -t 1 && echo tty || echo pipe'");
    let run = || {
        let out = Command::new("script")
            .args(["-qec", &inner, "/dev/null"])
            .env("MEMO_CACHE_DIR", &s.cache)
            .current_dir(s.dir.path())
            .stdin(Stdio::null())
            .output()
            .unwrap();
        String::from_utf8_lossy(&out.stdout).into_owned()
    };
    assert!(run().contains("tty"), "the command didn't see a terminal");
    assert!(run().contains("tty"), "the replay changed the output");
    assert!(Path::new(&s.cache)
        .join("v1")
        .read_dir()
        .unwrap()
        .next()
        .is_some());
}
