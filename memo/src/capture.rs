//! Passes a command's standard output and error through while recording
//! them, and replays a recording.
//!
//! A stream that is a terminal for memo is a pseudo-terminal for the command,
//! so the command sees `isatty` the same way it would without memo and keeps
//! its colors and line buffering.

use std::io;
use std::mem::zeroed;
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};
use std::sync::atomic::{AtomicBool, Ordering};
use std::sync::{Arc, Mutex};
use std::thread::JoinHandle;
use std::time::{Duration, Instant};

/// Output beyond this many bytes is passed through but not cached.
pub const MAX_OUTPUT: usize = 64 << 20;

pub const STDOUT: u8 = 1;
pub const STDERR: u8 = 2;

#[derive(Debug, Default)]
pub struct Captured {
    /// Output in arrival order, as (stream, bytes) with adjacent writes to the
    /// same stream merged.
    pub chunks: Vec<(u8, Vec<u8>)>,
    pub len: usize,
    pub overflow: bool,
    /// memo's own output was closed, so the command's output was cut off.
    pub broken_pipe: bool,
}

impl Captured {
    fn push(&mut self, stream: u8, data: &[u8]) {
        if self.overflow {
            return;
        }
        if self.len + data.len() > MAX_OUTPUT {
            self.overflow = true;
            self.chunks.clear();
            return;
        }
        self.len += data.len();
        match self.chunks.last_mut() {
            Some((s, buf)) if *s == stream => buf.extend_from_slice(data),
            _ => self.chunks.push((stream, data.to_vec())),
        }
    }
}

pub struct Capture {
    threads: Vec<JoinHandle<()>>,
    state: Arc<Mutex<Captured>>,
    stop: Arc<AtomicBool>,
}

/// The ends of the capture streams that the command writes to.
pub struct ChildIo {
    pub stdout: OwnedFd,
    pub stderr: OwnedFd,
}

pub fn isatty(fd: RawFd) -> bool {
    // SAFETY: isatty only inspects the descriptor.
    unsafe { libc::isatty(fd) == 1 }
}

fn check(r: libc::c_int) -> io::Result<libc::c_int> {
    if r < 0 {
        Err(io::Error::last_os_error())
    } else {
        Ok(r)
    }
}

fn cloexec(fd: RawFd) -> io::Result<()> {
    // SAFETY: fcntl on a descriptor this process owns.
    check(unsafe { libc::fcntl(fd, libc::F_SETFD, libc::FD_CLOEXEC) }).map(|_| ())
}

/// Opens a pseudo-terminal with the window size of `like`. Returns the
/// master, which memo reads, and the slave, which the command writes to.
fn open_pty(like: RawFd) -> io::Result<(OwnedFd, OwnedFd)> {
    // SAFETY: plain C structs, filled in by the calls below.
    let mut ws: libc::winsize = unsafe { zeroed() };
    // SAFETY: TIOCGWINSZ writes one winsize; failure leaves it zeroed.
    unsafe { libc::ioctl(like, libc::TIOCGWINSZ, &mut ws) };
    let (mut master, mut slave) = (-1, -1);
    // SAFETY: openpty writes two descriptors; null name and termios are allowed.
    check(unsafe {
        libc::openpty(
            &mut master,
            &mut slave,
            std::ptr::null_mut(),
            std::ptr::null(),
            &ws,
        )
    })?;
    // SAFETY: openpty succeeded, so both descriptors are open and ours.
    let (master, slave) = unsafe { (OwnedFd::from_raw_fd(master), OwnedFd::from_raw_fd(slave)) };
    cloexec(master.as_raw_fd())?;
    cloexec(slave.as_raw_fd())?;
    // Keep the bytes exactly as written: no \n to \r\n translation.
    // SAFETY: termios is plain data; tcgetattr fills it.
    let mut t: libc::termios = unsafe { zeroed() };
    // SAFETY: valid descriptor and termios pointer.
    if unsafe { libc::tcgetattr(slave.as_raw_fd(), &mut t) } == 0 {
        t.c_oflag &= !libc::OPOST;
        // SAFETY: as above.
        unsafe { libc::tcsetattr(slave.as_raw_fd(), libc::TCSANOW, &t) };
    }
    Ok((master, slave))
}

fn pipe() -> io::Result<(OwnedFd, OwnedFd)> {
    let mut fds = [-1; 2];
    // SAFETY: pipe2 writes two descriptors.
    check(unsafe { libc::pipe2(fds.as_mut_ptr(), libc::O_CLOEXEC) })?;
    // SAFETY: pipe2 succeeded.
    Ok(unsafe { (OwnedFd::from_raw_fd(fds[0]), OwnedFd::from_raw_fd(fds[1])) })
}

/// Writes all of `data` to `fd`, waiting if the descriptor is non-blocking.
pub fn write_all(fd: RawFd, mut data: &[u8]) -> io::Result<()> {
    while !data.is_empty() {
        // SAFETY: data is a valid buffer of data.len() bytes.
        let n = unsafe { libc::write(fd, data.as_ptr().cast(), data.len()) };
        if n < 0 {
            let e = io::Error::last_os_error();
            match e.kind() {
                io::ErrorKind::Interrupted => continue,
                io::ErrorKind::WouldBlock => {
                    let mut p = libc::pollfd {
                        fd,
                        events: libc::POLLOUT,
                        revents: 0,
                    };
                    // SAFETY: one valid pollfd.
                    unsafe { libc::poll(&mut p, 1, -1) };
                    continue;
                }
                _ => return Err(e),
            }
        }
        data = &data[n as usize..];
    }
    Ok(())
}

impl Capture {
    /// Starts capturing. The returned descriptors go to the command; drop
    /// every copy of them in memo once the command has started, or the
    /// capture never sees the end of the output.
    pub fn start() -> io::Result<(Capture, ChildIo)> {
        let state = Arc::new(Mutex::new(Captured::default()));
        let stop = Arc::new(AtomicBool::new(false));
        let mut threads = Vec::new();
        let mut ends = Vec::new();
        for (stream, ours) in [(STDOUT, 1), (STDERR, 2)] {
            let (read, write) = if isatty(ours) {
                open_pty(ours)?
            } else {
                pipe()?
            };
            let (state, stop) = (state.clone(), stop.clone());
            threads.push(std::thread::spawn(move || {
                pump(stream, read, ours, &state, &stop)
            }));
            ends.push(write);
        }
        let stderr = ends.pop().expect("two streams");
        let stdout = ends.pop().expect("two streams");
        Ok((
            Capture {
                threads,
                state,
                stop,
            },
            ChildIo { stdout, stderr },
        ))
    }

    /// Waits for the output to end and returns it. If background processes
    /// may still hold the streams open, waits at most `patience`.
    pub fn finish(self, patience: Option<Duration>) -> Captured {
        if let Some(p) = patience {
            let deadline = Instant::now() + p;
            while Instant::now() < deadline && self.threads.iter().any(|t| !t.is_finished()) {
                std::thread::sleep(Duration::from_millis(5));
            }
            self.stop.store(true, Ordering::SeqCst);
        }
        for t in self.threads {
            let _ = t.join();
        }
        let mut state = self.state.lock().unwrap_or_else(|e| e.into_inner());
        std::mem::take(&mut *state)
    }
}

fn pump(stream: u8, src: OwnedFd, dst: RawFd, state: &Mutex<Captured>, stop: &AtomicBool) {
    let mut buf = vec![0u8; 64 << 10];
    loop {
        if stop.load(Ordering::SeqCst) {
            return;
        }
        let mut p = libc::pollfd {
            fd: src.as_raw_fd(),
            events: libc::POLLIN,
            revents: 0,
        };
        // SAFETY: one valid pollfd.
        let r = unsafe { libc::poll(&mut p, 1, 50) };
        if r == 0 {
            continue;
        }
        if r < 0 {
            if io::Error::last_os_error().kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return;
        }
        // SAFETY: buf is a valid buffer of buf.len() bytes.
        let n = unsafe { libc::read(src.as_raw_fd(), buf.as_mut_ptr().cast(), buf.len()) };
        if n == 0 {
            return;
        }
        if n < 0 {
            match io::Error::last_os_error().kind() {
                io::ErrorKind::Interrupted | io::ErrorKind::WouldBlock => continue,
                // A pseudo-terminal master reads EIO once every slave closed.
                _ => return,
            }
        }
        let data = &buf[..n as usize];
        if let Err(e) = write_all(dst, data) {
            if e.kind() == io::ErrorKind::BrokenPipe {
                // Close our end so the command sees the closed pipe too.
                state.lock().unwrap_or_else(|e| e.into_inner()).broken_pipe = true;
                return;
            }
        }
        state
            .lock()
            .unwrap_or_else(|e| e.into_inner())
            .push(stream, data);
    }
}

/// Encodes chunks as a sequence of (stream byte, little-endian u32 length,
/// bytes) records.
pub fn encode(chunks: &[(u8, Vec<u8>)]) -> Vec<u8> {
    let mut out = Vec::with_capacity(chunks.iter().map(|c| c.1.len() + 5).sum());
    for (stream, data) in chunks {
        for part in data.chunks(u32::MAX as usize) {
            out.push(*stream);
            out.extend_from_slice(&(part.len() as u32).to_le_bytes());
            out.extend_from_slice(part);
        }
    }
    out
}

pub fn decode(mut b: &[u8]) -> io::Result<Vec<(u8, Vec<u8>)>> {
    let bad = || io::Error::new(io::ErrorKind::InvalidData, "corrupt output record");
    let mut out = Vec::new();
    while !b.is_empty() {
        if b.len() < 5 {
            return Err(bad());
        }
        let len = u32::from_le_bytes([b[1], b[2], b[3], b[4]]) as usize;
        let data = b.get(5..5 + len).ok_or_else(bad)?;
        out.push((b[0], data.to_vec()));
        b = &b[5 + len..];
    }
    Ok(out)
}

/// Writes recorded output to memo's own standard output and error. Stops
/// quietly if a reader closed the pipe.
pub fn replay(chunks: &[(u8, Vec<u8>)]) {
    for (stream, data) in chunks {
        let fd = if *stream == STDERR { 2 } else { 1 };
        if write_all(fd, data).is_err() {
            return;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn merges_adjacent_writes() {
        let mut c = Captured::default();
        c.push(STDOUT, b"a");
        c.push(STDOUT, b"b");
        c.push(STDERR, b"!");
        c.push(STDOUT, b"c");
        assert_eq!(
            c.chunks,
            vec![
                (STDOUT, b"ab".to_vec()),
                (STDERR, b"!".to_vec()),
                (STDOUT, b"c".to_vec())
            ]
        );
        assert_eq!(c.len, 4);
    }

    #[test]
    fn overflow_drops_the_recording() {
        let mut c = Captured::default();
        c.push(STDOUT, &vec![0; MAX_OUTPUT]);
        assert!(!c.overflow);
        c.push(STDOUT, b"x");
        assert!(c.overflow);
        assert!(c.chunks.is_empty());
    }

    #[test]
    fn encoding_round_trips() {
        let chunks = vec![
            (STDOUT, b"hello\n".to_vec()),
            (STDERR, vec![b'!']),
            (STDOUT, vec![0, 1]),
        ];
        assert_eq!(decode(&encode(&chunks)).unwrap(), chunks);
        assert!(decode(&[1, 9, 0, 0, 0, b'x']).is_err());
    }
}
