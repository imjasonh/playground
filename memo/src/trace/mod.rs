//! Runs a command under a seccomp user-notification filter and records the
//! file-system and network calls of the command and all its descendants.
//!
//! A dedicated thread answers notifications. memo is a child subreaper, so
//! orphaned descendants stay its children: it can still read their memory
//! and knows when the last one exits. If any outlive the command, a forked
//! helper keeps answering their notifications, because a filter whose
//! listener is closed fails every traced call with `ENOSYS`.

mod mem;
mod seccomp;
mod syscalls;

use crate::record::{Outcome, Recorder};
use std::io::{self, Read, Write};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::os::unix::net::UnixStream;
use std::os::unix::process::CommandExt;
use std::panic::{catch_unwind, AssertUnwindSafe};
use std::process::Command;
use std::sync::atomic::{AtomicI32, Ordering};
use std::time::{Duration, Instant};

/// How long descendants may keep running after the command exits before
/// memo treats them as background processes.
const GRACE: Duration = Duration::from_millis(250);

static ROOT_PID: AtomicI32 = AtomicI32::new(0);

pub struct Finished {
    /// The command's wait status.
    pub status: i32,
    pub outcome: Outcome,
    /// Descendants were still running when memo stopped waiting.
    pub lingering: bool,
}

pub enum Error {
    /// The system can't trace the command.
    Setup(io::Error),
    /// The command couldn't be started, for example because it doesn't exist.
    Spawn(io::Error),
}

struct TracerEnd {
    recorder: Recorder,
    listener: Option<OwnedFd>,
    got_listener: bool,
}

/// Runs `cmd` to completion while recording into `recorder`. If
/// `stdin_id` is set, reads of that file (memo's standard input) are
/// reported as [`crate::record::Event::StdinRead`].
pub fn run(
    mut cmd: Command,
    stdin_id: Option<(u64, u64)>,
    recorder: Recorder,
) -> Result<Finished, Error> {
    // SAFETY: setting the subreaper attribute has no memory effects.
    unsafe { libc::prctl(libc::PR_SET_CHILD_SUBREAPER, 1, 0, 0, 0) };
    let (parent_sock, child_sock) = seqpacket_pair().map_err(Error::Setup)?;
    let child_fd = child_sock.as_raw_fd();
    let filter = seccomp::Filter::new(
        syscalls::AUDIT_ARCH,
        &syscalls::rules(stdin_id.is_some(), child_fd),
    );
    // SAFETY: the closure only resets signal dispositions and makes the
    // system calls in install_and_send, all safe between fork and exec.
    unsafe {
        cmd.pre_exec(move || {
            for sig in [libc::SIGINT, libc::SIGQUIT, libc::SIGPIPE] {
                libc::signal(sig, libc::SIG_DFL);
            }
            seccomp::install_and_send(&filter, child_fd)
        });
    }
    let (ctl, ctl_tracer) = UnixStream::pair().map_err(Error::Setup)?;
    let tracer =
        std::thread::spawn(move || tracer_loop(parent_sock, ctl_tracer, recorder, stdin_id));

    let signals = SignalGuard::install();
    let spawned = cmd.spawn();
    drop(child_sock);
    // Drops memo's copies of the command's standard streams.
    drop(cmd);
    let child = match spawned {
        Ok(child) => child,
        Err(e) => {
            let _ = (&ctl).write_all(b"d");
            let got_listener = tracer.join().is_ok_and(|end| end.got_listener);
            return Err(if got_listener {
                Error::Spawn(e)
            } else {
                Error::Setup(e)
            });
        }
    };
    let root = child.id() as i32;
    ROOT_PID.store(root, Ordering::SeqCst);
    let status = wait_for(root);
    ROOT_PID.store(0, Ordering::SeqCst);
    drop(signals);

    let lingering = !reap_until(Instant::now() + GRACE);
    let _ = (&ctl).write_all(if lingering { b"l" } else { b"d" });
    let end = match tracer.join() {
        Ok(end) => end,
        Err(_) => {
            let outcome = Outcome {
                reasons: vec!["memo's tracer failed".into()],
                ..Outcome::default()
            };
            return Ok(Finished {
                status,
                outcome,
                lingering,
            });
        }
    };
    let mut recorder = end.recorder;
    if lingering {
        recorder.add_reason("left background processes running after it exited");
        if let Some(listener) = end.listener {
            babysit(listener);
        }
    }
    Ok(Finished {
        status,
        outcome: recorder.finish(),
        lingering,
    })
}

fn seqpacket_pair() -> io::Result<(OwnedFd, OwnedFd)> {
    let mut fds = [-1; 2];
    // SAFETY: socketpair writes two descriptors.
    let r = unsafe {
        libc::socketpair(
            libc::AF_UNIX,
            libc::SOCK_SEQPACKET | libc::SOCK_CLOEXEC,
            0,
            fds.as_mut_ptr(),
        )
    };
    if r < 0 {
        return Err(io::Error::last_os_error());
    }
    // SAFETY: socketpair succeeded, so both descriptors are ours.
    Ok(unsafe { (OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1])) })
}

fn tracer_loop(
    sock: OwnedFd,
    mut ctl: UnixStream,
    mut recorder: Recorder,
    stdin_id: Option<(u64, u64)>,
) -> TracerEnd {
    let listener = match seccomp::recv_listener(&sock) {
        Ok(l) => l,
        Err(_) => {
            return TracerEnd {
                recorder,
                listener: None,
                got_listener: false,
            }
        }
    };
    drop(sock);
    let lfd = listener.as_raw_fd();
    let mut sync = SyncWake::new(lfd);
    let mut listening = true;
    loop {
        let mut fds = [
            libc::pollfd {
                fd: if listening { lfd } else { -1 },
                events: libc::POLLIN,
                revents: 0,
            },
            libc::pollfd {
                fd: ctl.as_raw_fd(),
                events: libc::POLLIN,
                revents: 0,
            },
        ];
        // SAFETY: two valid pollfds.
        if unsafe { libc::poll(fds.as_mut_ptr(), 2, -1) } < 0 {
            continue;
        }
        if fds[0].revents & libc::POLLIN != 0 {
            handle(lfd, &mut recorder, stdin_id, &mut sync);
            continue;
        }
        if fds[0].revents & (libc::POLLHUP | libc::POLLERR | libc::POLLNVAL) != 0 {
            listening = false;
        }
        if fds[1].revents != 0 {
            let mut msg = [0u8; 1];
            let linger = matches!(ctl.read(&mut msg), Ok(1)) && msg[0] == b'l';
            return TracerEnd {
                recorder,
                listener: linger.then_some(listener),
                got_listener: true,
            };
        }
    }
}

/// Keeps synchronous wake-up on while the command traps one call at a time,
/// and turns it off for good once calls queue up behind each other, which
/// means several threads or processes are trapping at once.
struct SyncWake {
    lfd: RawFd,
    on: bool,
    handled: u32,
    queued: u32,
}

impl SyncWake {
    const WINDOW: u32 = 64;

    fn new(lfd: RawFd) -> SyncWake {
        seccomp::sync_wake_up(lfd, true);
        SyncWake {
            lfd,
            on: true,
            handled: 0,
            queued: 0,
        }
    }

    /// Runs while the thread behind the current notification is still
    /// blocked, so a pending notification must come from another thread.
    fn before_reply(&mut self) {
        if !self.on {
            return;
        }
        let mut p = libc::pollfd {
            fd: self.lfd,
            events: libc::POLLIN,
            revents: 0,
        };
        // SAFETY: one valid pollfd; a zero timeout doesn't block.
        if unsafe { libc::poll(&mut p, 1, 0) } > 0 && p.revents & libc::POLLIN != 0 {
            self.queued += 1;
        }
        self.handled += 1;
        if self.handled == Self::WINDOW {
            if self.queued * 8 > self.handled {
                self.on = false;
                seccomp::sync_wake_up(self.lfd, false);
            }
            self.handled = 0;
            self.queued = 0;
        }
    }
}

fn handle(lfd: RawFd, recorder: &mut Recorder, stdin_id: Option<(u64, u64)>, sync: &mut SyncWake) {
    let Ok(n) = seccomp::recv(lfd) else {
        return;
    };
    if let Some(errno) = syscalls::refusal(&n) {
        seccomp::deny(lfd, n.id, errno);
        return;
    }
    let result = catch_unwind(AssertUnwindSafe(|| {
        let events = syscalls::decode(&n, stdin_id);
        if !events.is_empty() && seccomp::id_valid(lfd, n.id) {
            for ev in events {
                recorder.apply(ev);
            }
        }
    }));
    if result.is_err() {
        recorder.add_reason("memo hit an internal error while tracing");
    }
    sync.before_reply();
    seccomp::allow(lfd, n.id);
}

fn wait_for(root: i32) -> i32 {
    loop {
        let mut status = 0;
        // SAFETY: waitpid writes one int.
        let pid = unsafe { libc::waitpid(-1, &mut status, 0) };
        if pid == root {
            return status;
        }
        if pid < 0 && io::Error::last_os_error().raw_os_error() == Some(libc::ECHILD) {
            return 1 << 8;
        }
    }
}

/// Reaps orphaned descendants until none are left or `deadline` passes.
/// Returns whether all of them exited.
fn reap_until(deadline: Instant) -> bool {
    loop {
        let mut status = 0;
        // SAFETY: waitpid writes one int.
        let pid = unsafe { libc::waitpid(-1, &mut status, libc::WNOHANG) };
        if pid > 0 {
            continue;
        }
        if pid < 0 {
            match io::Error::last_os_error().raw_os_error() {
                Some(libc::EINTR) => continue,
                _ => return true,
            }
        }
        if Instant::now() >= deadline {
            return false;
        }
        std::thread::sleep(Duration::from_millis(2));
    }
}

/// Forks a helper that lets the traced calls of background processes run
/// until the last one exits. It only makes system calls, so it is safe to
/// run in the child of a multithreaded fork.
fn babysit(listener: OwnedFd) {
    let lfd = listener.as_raw_fd();
    // SAFETY: the child calls only async-signal-safe functions, then _exit.
    unsafe {
        if libc::fork() != 0 {
            return;
        }
        libc::setsid();
        // Move the listener out of the way first: if memo started with a
        // standard stream closed, the listener may be descriptor 0, 1, or 2.
        let high = libc::fcntl(lfd, libc::F_DUPFD, 10);
        let null = libc::open(c"/dev/null".as_ptr(), libc::O_RDWR);
        for fd in 0..3 {
            libc::dup2(null, fd);
        }
        libc::dup2(high, 3);
        if libc::syscall(libc::SYS_close_range, 4u32, u32::MAX, 0u32) != 0 {
            for fd in 4..4096 {
                libc::close(fd);
            }
        }
        loop {
            let mut p = libc::pollfd {
                fd: 3,
                events: libc::POLLIN,
                revents: 0,
            };
            if libc::poll(&mut p, 1, -1) < 0 {
                continue;
            }
            if p.revents & libc::POLLIN != 0 {
                if let Ok(n) = seccomp::recv(3) {
                    seccomp::allow(3, n.id);
                }
            } else if p.revents != 0 {
                libc::_exit(0);
            }
        }
    }
}

/// While the command runs, memo ignores the terminal's interrupt and quit
/// signals (the command gets them too) and forwards SIGTERM and SIGHUP.
struct SignalGuard;

extern "C" fn forward(sig: libc::c_int) {
    let pid = ROOT_PID.load(Ordering::SeqCst);
    if pid > 0 {
        // SAFETY: kill is async-signal-safe.
        unsafe { libc::kill(pid, sig) };
    }
}

impl SignalGuard {
    fn install() -> SignalGuard {
        // SAFETY: installs process-wide dispositions; `forward` is
        // async-signal-safe.
        unsafe {
            libc::signal(libc::SIGINT, libc::SIG_IGN);
            libc::signal(libc::SIGQUIT, libc::SIG_IGN);
            let mut sa: libc::sigaction = std::mem::zeroed();
            sa.sa_sigaction = forward as *const () as usize;
            sa.sa_flags = libc::SA_RESTART;
            libc::sigemptyset(&mut sa.sa_mask);
            libc::sigaction(libc::SIGTERM, &sa, std::ptr::null_mut());
            libc::sigaction(libc::SIGHUP, &sa, std::ptr::null_mut());
        }
        SignalGuard
    }
}

impl Drop for SignalGuard {
    fn drop(&mut self) {
        // SAFETY: restores default dispositions.
        unsafe {
            for sig in [libc::SIGINT, libc::SIGQUIT, libc::SIGTERM, libc::SIGHUP] {
                libc::signal(sig, libc::SIG_DFL);
            }
        }
    }
}
