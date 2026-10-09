//! The seccomp user-notification filter: building it, installing it in the
//! child, passing its listener to the parent, and the notification ioctls.
//!
//! The filter returns `SECCOMP_RET_USER_NOTIF` for the traced system calls,
//! which blocks the calling thread until the listener answers. memo always
//! answers `SECCOMP_USER_NOTIF_FLAG_CONTINUE`, so the call then runs as if
//! there were no filter. Other system calls never leave the kernel.

use std::io;
use std::mem::{size_of, zeroed};
use std::os::fd::{AsRawFd, FromRawFd, OwnedFd, RawFd};

const SECCOMP_SET_MODE_FILTER: libc::c_ulong = 1;
const SECCOMP_FILTER_FLAG_NEW_LISTENER: libc::c_ulong = 1 << 3;
const SECCOMP_RET_USER_NOTIF: u32 = 0x7fc0_0000;
const SECCOMP_RET_ALLOW: u32 = 0x7fff_0000;
const SECCOMP_USER_NOTIF_FLAG_CONTINUE: u32 = 1;

const NOTIF_RECV: u64 = 0xC050_2100;
const NOTIF_SEND: u64 = 0xC018_2101;
const NOTIF_ID_VALID: u64 = 0x4008_2102;
const NOTIF_SET_FLAGS: u64 = 0x4008_2104;
const SECCOMP_USER_NOTIF_FD_SYNC_WAKE_UP: u64 = 1;
/// The request number that kernels before 5.9 used for `NOTIF_ID_VALID`.
const NOTIF_ID_VALID_OLD: u64 = 0x8008_2102;

const BPF_LD_W_ABS: u16 = 0x20;
const BPF_JEQ_K: u16 = 0x15;
const BPF_JGE_K: u16 = 0x35;
const BPF_RET_K: u16 = 0x06;

const OFF_NR: u32 = 0;
const OFF_ARCH: u32 = 4;
const OFF_ARGS: u32 = 16;

#[cfg(target_arch = "x86_64")]
const X32_SYSCALL_BIT: u32 = 0x4000_0000;

#[repr(C)]
#[derive(Clone, Copy)]
struct SockFilter {
    code: u16,
    jt: u8,
    jf: u8,
    k: u32,
}

#[repr(C)]
struct SockFprog {
    len: u16,
    filter: *const SockFilter,
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct SeccompData {
    pub nr: i32,
    pub arch: u32,
    pub instruction_pointer: u64,
    pub args: [u64; 6],
}

#[repr(C)]
#[derive(Clone, Copy, Debug)]
pub struct Notif {
    pub id: u64,
    pub pid: u32,
    pub flags: u32,
    pub data: SeccompData,
}

/// Room for a `struct seccomp_notif` from a kernel newer than this file.
#[repr(C, align(8))]
struct NotifBuf {
    notif: Notif,
    _spare: [u8; 176],
}

#[repr(C)]
struct NotifResp {
    id: u64,
    val: i64,
    error: i32,
    flags: u32,
}

/// When a traced call notifies the listener.
pub enum Rule {
    Always(i64),
    /// Only when argument `arg` equals `value`.
    ArgEq(i64, u8, u64),
    /// Unless argument `arg` equals `value`.
    ArgNe(i64, u8, u64),
}

pub struct Filter(Vec<SockFilter>);

fn stmt(code: u16, k: u32) -> SockFilter {
    SockFilter {
        code,
        jt: 0,
        jf: 0,
        k,
    }
}

fn jump(code: u16, k: u32, jt: u8, jf: u8) -> SockFilter {
    SockFilter { code, jt, jf, k }
}

impl Filter {
    /// Builds a filter for the native architecture. Calls from any other ABI
    /// (32-bit or x32 processes) always notify, so memo can tell that it
    /// can't decode them.
    pub fn new(arch: u32, rules: &[Rule]) -> Filter {
        let ret_notify = stmt(BPF_RET_K, SECCOMP_RET_USER_NOTIF);
        let ret_allow = stmt(BPF_RET_K, SECCOMP_RET_ALLOW);
        let mut p = vec![
            stmt(BPF_LD_W_ABS, OFF_ARCH),
            jump(BPF_JEQ_K, arch, 1, 0),
            ret_notify,
            stmt(BPF_LD_W_ABS, OFF_NR),
        ];
        #[cfg(target_arch = "x86_64")]
        p.extend([jump(BPF_JGE_K, X32_SYSCALL_BIT, 0, 1), ret_notify]);
        for rule in rules {
            match *rule {
                Rule::Always(nr) => {
                    p.push(jump(BPF_JEQ_K, nr as u32, 0, 1));
                    p.push(ret_notify);
                }
                Rule::ArgEq(nr, arg, value) | Rule::ArgNe(nr, arg, value) => {
                    let eq = matches!(rule, Rule::ArgEq(..));
                    let lo = OFF_ARGS + 8 * arg as u32;
                    p.push(jump(BPF_JEQ_K, nr as u32, 0, 6));
                    p.push(stmt(BPF_LD_W_ABS, lo));
                    if eq {
                        p.push(jump(BPF_JEQ_K, value as u32, 0, 3));
                        p.push(stmt(BPF_LD_W_ABS, lo + 4));
                        p.push(jump(BPF_JEQ_K, (value >> 32) as u32, 0, 1));
                    } else {
                        p.push(jump(BPF_JEQ_K, value as u32, 0, 2));
                        p.push(stmt(BPF_LD_W_ABS, lo + 4));
                        p.push(jump(BPF_JEQ_K, (value >> 32) as u32, 1, 0));
                    }
                    p.push(ret_notify);
                    p.push(ret_allow);
                }
            }
        }
        p.push(ret_allow);
        Filter(p)
    }
}

/// Installs `filter` in the calling process and sends the listener over
/// `sock`. Runs in the forked child before `exec`, so it makes only system
/// calls and doesn't allocate.
///
/// # Safety
///
/// Call only in a freshly forked child, as from `Command::pre_exec`.
pub unsafe fn install_and_send(filter: &Filter, sock: RawFd) -> io::Result<()> {
    if libc::prctl(libc::PR_SET_NO_NEW_PRIVS, 1, 0, 0, 0) != 0 {
        return Err(io::Error::last_os_error());
    }
    let prog = SockFprog {
        len: filter.0.len() as u16,
        filter: filter.0.as_ptr(),
    };
    let fd = libc::syscall(
        libc::SYS_seccomp,
        SECCOMP_SET_MODE_FILTER,
        SECCOMP_FILTER_FLAG_NEW_LISTENER,
        &prog as *const SockFprog,
    );
    if fd < 0 {
        return Err(io::Error::last_os_error());
    }
    let fd = fd as RawFd;
    let result = send_fd(sock, fd);
    libc::close(fd);
    result
}

unsafe fn send_fd(sock: RawFd, fd: RawFd) -> io::Result<()> {
    let mut byte = [0u8; 1];
    let mut iov = libc::iovec {
        iov_base: byte.as_mut_ptr().cast(),
        iov_len: 1,
    };
    let mut control = [0u64; 4];
    let mut msg: libc::msghdr = zeroed();
    msg.msg_iov = &mut iov;
    msg.msg_iovlen = 1;
    msg.msg_control = control.as_mut_ptr().cast();
    msg.msg_controllen = libc::CMSG_SPACE(size_of::<RawFd>() as u32) as _;
    let cmsg = libc::CMSG_FIRSTHDR(&msg);
    (*cmsg).cmsg_level = libc::SOL_SOCKET;
    (*cmsg).cmsg_type = libc::SCM_RIGHTS;
    (*cmsg).cmsg_len = libc::CMSG_LEN(size_of::<RawFd>() as u32) as _;
    std::ptr::write_unaligned(libc::CMSG_DATA(cmsg).cast::<RawFd>(), fd);
    if libc::sendmsg(sock, &msg, 0) < 0 {
        return Err(io::Error::last_os_error());
    }
    Ok(())
}

/// Receives the listener sent by [`install_and_send`]. Fails with
/// `UnexpectedEof` if the child exited without sending one.
pub fn recv_listener(sock: &OwnedFd) -> io::Result<OwnedFd> {
    let mut byte = [0u8; 1];
    let mut iov = libc::iovec {
        iov_base: byte.as_mut_ptr().cast(),
        iov_len: 1,
    };
    let mut control = [0u64; 4];
    // SAFETY: msghdr is plain data; every pointer set below outlives the call.
    let mut msg: libc::msghdr = unsafe { zeroed() };
    msg.msg_iov = &mut iov;
    msg.msg_iovlen = 1;
    msg.msg_control = control.as_mut_ptr().cast();
    msg.msg_controllen = std::mem::size_of_val(&control) as _;
    loop {
        // SAFETY: `msg` describes valid buffers.
        let n = unsafe { libc::recvmsg(sock.as_raw_fd(), &mut msg, libc::MSG_CMSG_CLOEXEC) };
        if n < 0 {
            let e = io::Error::last_os_error();
            if e.kind() == io::ErrorKind::Interrupted {
                continue;
            }
            return Err(e);
        }
        if n == 0 {
            return Err(io::ErrorKind::UnexpectedEof.into());
        }
        break;
    }
    // SAFETY: CMSG_FIRSTHDR reads only within msg_control.
    let cmsg = unsafe { libc::CMSG_FIRSTHDR(&msg) };
    if cmsg.is_null() {
        return Err(io::Error::other("no listener in the setup message"));
    }
    // SAFETY: cmsg points into `control`, which the kernel just filled.
    unsafe {
        if (*cmsg).cmsg_level != libc::SOL_SOCKET || (*cmsg).cmsg_type != libc::SCM_RIGHTS {
            return Err(io::Error::other("unexpected control message"));
        }
        let fd = std::ptr::read_unaligned(libc::CMSG_DATA(cmsg).cast::<RawFd>());
        Ok(OwnedFd::from_raw_fd(fd))
    }
}

/// Turns synchronous wake-up on or off (Linux 6.6 and later). When it's on,
/// the kernel hands the CPU straight from the blocked thread to the listener
/// and back, which makes each round trip about three times faster, but it
/// serializes threads that trap at the same time. Older kernels reject the
/// request, which is harmless.
pub fn sync_wake_up(listener: RawFd, on: bool) {
    let flags = if on {
        SECCOMP_USER_NOTIF_FD_SYNC_WAKE_UP
    } else {
        0
    };
    // SAFETY: the ioctl takes the flags by value.
    unsafe { libc::ioctl(listener, NOTIF_SET_FLAGS as _, flags) };
}

/// Receives the next notification. Fails with `ENOENT` if the calling thread
/// died before the notification could be read.
pub fn recv(listener: RawFd) -> io::Result<Notif> {
    // SAFETY: the kernel requires a zeroed buffer and writes at most the size
    // that it reports, which fits in NotifBuf.
    let mut buf: NotifBuf = unsafe { zeroed() };
    loop {
        // SAFETY: `buf` is large enough for the kernel's seccomp_notif.
        let r = unsafe { libc::ioctl(listener, NOTIF_RECV as _, &mut buf) };
        if r == 0 {
            return Ok(buf.notif);
        }
        let e = io::Error::last_os_error();
        if e.kind() != io::ErrorKind::Interrupted {
            return Err(e);
        }
    }
}

/// Reports whether notification `id` is still pending, so the memory read
/// for it came from the thread that made the call.
pub fn id_valid(listener: RawFd, id: u64) -> bool {
    let mut id = id;
    // SAFETY: the ioctl reads one u64 from `id`.
    let r = unsafe { libc::ioctl(listener, NOTIF_ID_VALID as _, &mut id) };
    if r == 0 {
        return true;
    }
    if io::Error::last_os_error().raw_os_error() == Some(libc::ENOENT) {
        return false;
    }
    // SAFETY: as above, with the pre-5.9 request number.
    unsafe { libc::ioctl(listener, NOTIF_ID_VALID_OLD as _, &mut id) == 0 }
}

/// Lets the call behind notification `id` run.
pub fn allow(listener: RawFd, id: u64) {
    send(
        listener,
        NotifResp {
            id,
            val: 0,
            error: 0,
            flags: SECCOMP_USER_NOTIF_FLAG_CONTINUE,
        },
    );
}

/// Fails the call behind notification `id` with `errno` without running it.
pub fn deny(listener: RawFd, id: u64, errno: i32) {
    send(
        listener,
        NotifResp {
            id,
            val: 0,
            error: -errno,
            flags: 0,
        },
    );
}

fn send(listener: RawFd, mut resp: NotifResp) {
    loop {
        // SAFETY: the ioctl reads one seccomp_notif_resp from `resp`.
        let r = unsafe { libc::ioctl(listener, NOTIF_SEND as _, &mut resp) };
        if r == 0 || io::Error::last_os_error().kind() != io::ErrorKind::Interrupted {
            return;
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn notif_layout_matches_the_kernel() {
        assert_eq!(size_of::<SeccompData>(), 64);
        assert_eq!(size_of::<Notif>(), 80);
        assert_eq!(size_of::<NotifResp>(), 24);
    }

    #[test]
    fn filter_jumps_stay_in_bounds() {
        let f = Filter::new(
            0xC000_003E,
            &[Rule::Always(2), Rule::ArgEq(0, 0, 0), Rule::ArgNe(46, 0, 7)],
        );
        let len = f.0.len();
        for (i, ins) in f.0.iter().enumerate() {
            if ins.code == BPF_JEQ_K || ins.code == BPF_JGE_K {
                assert!(i + 1 + (ins.jt as usize) < len);
                assert!(i + 1 + (ins.jf as usize) < len);
            }
        }
        assert_eq!(f.0.last().unwrap().k, SECCOMP_RET_ALLOW);
    }
}
