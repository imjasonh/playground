//! The traced system calls and how their arguments become [`Event`]s.

use super::mem::{normalize, Mem};
use super::seccomp::{Notif, Rule};
use crate::net::{parse_sockaddr, NetTarget};
use crate::record::Event;
use std::os::unix::ffi::OsStringExt;
use std::os::unix::fs::MetadataExt;
use std::path::PathBuf;

#[cfg(target_arch = "x86_64")]
pub const AUDIT_ARCH: u32 = 0xC000_003E;
#[cfg(target_arch = "aarch64")]
pub const AUDIT_ARCH: u32 = 0xC000_00B7;

// System calls added after the unified numbering in Linux 5.1 have the same
// number on every architecture. They're spelled out because older releases
// of the libc crate don't define all of them.
const SYS_IO_URING_SETUP: i64 = 425;
const SYS_OPEN_TREE: i64 = 428;
const SYS_MOVE_MOUNT: i64 = 429;
const SYS_FSOPEN: i64 = 430;
const SYS_FSCONFIG: i64 = 431;
const SYS_FSMOUNT: i64 = 432;
const SYS_FSPICK: i64 = 433;
const SYS_OPENAT2: i64 = 437;
const SYS_FACCESSAT2: i64 = 439;
const SYS_MOUNT_SETATTR: i64 = 442;
const SYS_FCHMODAT2: i64 = 452;

const FOREIGN_ABI: &str =
    "ran a program for another ABI (32-bit or x32), whose system calls memo can't decode";
const MOUNTS: &str = "changed mounts or namespaces, so memo can't follow its paths";

const AT_FDCWD: u64 = libc::AT_FDCWD as u64;

/// System calls that always notify.
const ALWAYS: &[i64] = &[
    libc::SYS_openat,
    SYS_OPENAT2,
    libc::SYS_newfstatat,
    libc::SYS_statx,
    libc::SYS_faccessat,
    SYS_FACCESSAT2,
    libc::SYS_readlinkat,
    libc::SYS_execve,
    libc::SYS_execveat,
    libc::SYS_getdents64,
    libc::SYS_chdir,
    libc::SYS_truncate,
    libc::SYS_renameat,
    libc::SYS_renameat2,
    libc::SYS_unlinkat,
    libc::SYS_mkdirat,
    libc::SYS_linkat,
    libc::SYS_symlinkat,
    libc::SYS_fchmodat,
    SYS_FCHMODAT2,
    libc::SYS_fchownat,
    libc::SYS_utimensat,
    libc::SYS_mknodat,
    libc::SYS_connect,
    libc::SYS_bind,
    libc::SYS_sendto,
    libc::SYS_sendmmsg,
    libc::SYS_open_by_handle_at,
    SYS_IO_URING_SETUP,
    libc::SYS_mount,
    libc::SYS_umount2,
    libc::SYS_pivot_root,
    libc::SYS_chroot,
    libc::SYS_setns,
    SYS_OPEN_TREE,
    SYS_MOVE_MOUNT,
    SYS_FSOPEN,
    SYS_FSCONFIG,
    SYS_FSMOUNT,
    SYS_FSPICK,
    SYS_MOUNT_SETATTR,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_open,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_creat,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_stat,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_lstat,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_access,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_readlink,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_getdents,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_rename,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_unlink,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_rmdir,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_mkdir,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_link,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_symlink,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_chmod,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_chown,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_lchown,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_utime,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_utimes,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_futimesat,
    #[cfg(target_arch = "x86_64")]
    libc::SYS_mknod,
];

/// Calls that read from a file descriptor, and which argument holds it. They
/// notify only for descriptor 0, and only if standard input is a terminal or
/// a pipe that memo can't fingerprint.
const STDIN_READS: &[(i64, u8)] = &[
    (libc::SYS_read, 0),
    (libc::SYS_readv, 0),
    (libc::SYS_pread64, 0),
    (libc::SYS_preadv, 0),
    (libc::SYS_preadv2, 0),
    (libc::SYS_recvfrom, 0),
    (libc::SYS_recvmsg, 0),
    (libc::SYS_recvmmsg, 0),
    (libc::SYS_splice, 0),
    (libc::SYS_tee, 0),
    (libc::SYS_copy_file_range, 0),
    (libc::SYS_sendfile, 1),
];

/// Returns the filter rules. `setup_fd` is the child's end of the socket
/// that carries the listener; its own `sendmsg` must not notify, since
/// nobody is listening yet.
pub fn rules(trap_stdin: bool, setup_fd: i32) -> Vec<Rule> {
    let mut rules: Vec<Rule> = ALWAYS.iter().map(|&nr| Rule::Always(nr)).collect();
    rules.push(Rule::ArgNe(libc::SYS_sendmsg, 0, setup_fd as u64));
    if trap_stdin {
        for &(nr, arg) in STDIN_READS {
            rules.push(Rule::ArgEq(nr, arg, 0));
        }
    }
    rules
}

fn path(m: &Mem, dirfd: u64, addr: u64) -> Option<PathBuf> {
    let raw = m.read_cstr(addr).ok()?;
    if raw.is_empty() {
        return None;
    }
    m.resolve(dirfd as i32, &raw)
}

fn follows(flags: u64) -> bool {
    flags & libc::AT_SYMLINK_NOFOLLOW as u64 == 0
}

fn sockaddr(m: &Mem, addr: u64, len: u64) -> Option<NetTarget> {
    if addr == 0 || len < 2 {
        return None;
    }
    let mut buf = vec![0u8; (len as usize).min(128)];
    m.read_exact(addr, &mut buf).ok()?;
    Some(match parse_sockaddr(&buf)? {
        NetTarget::Unix(raw) => {
            let abs = if raw.first() == Some(&b'/') {
                normalize(&raw)
            } else {
                m.resolve(libc::AT_FDCWD, &raw)?
            };
            NetTarget::Unix(abs.into_os_string().into_vec())
        }
        other => other,
    })
}

/// Reads the destination of one `struct msghdr`, if it has one.
fn msg_dest(m: &Mem, msghdr: u64) -> Option<NetTarget> {
    let name = m.read_u64(msghdr).ok()?;
    let len = m.read_u32(msghdr + 8).ok()?;
    sockaddr(m, name, len as u64)
}

/// Reports a read of descriptor 0 only if it is still memo's standard input;
/// a shell inside the command may have redirected it to a file it opened.
fn stdin_read(m: &Mem, stdin_id: Option<(u64, u64)>) -> Option<Event> {
    let md = std::fs::metadata(format!("/proc/{}/fd/0", m.pid)).ok()?;
    (Some((md.dev(), md.ino())) == stdin_id).then_some(Event::StdinRead)
}

/// Returns the error to fail a call with instead of running it. `io_uring`
/// file operations never pass through system calls, so memo refuses to set
/// up a ring, as many container runtimes do. Programs then fall back to
/// ordinary system calls; libuv (Node.js), for example, does.
pub fn refusal(n: &Notif) -> Option<i32> {
    (n.data.arch == AUDIT_ARCH && n.data.nr as i64 == SYS_IO_URING_SETUP).then_some(libc::ENOSYS)
}

/// Decodes one notification. Returns no events for calls that can't affect
/// a cached result, such as `fstat` through `newfstatat` with `AT_EMPTY_PATH`.
pub fn decode(n: &Notif, stdin_id: Option<(u64, u64)>) -> Vec<Event> {
    if n.data.arch != AUDIT_ARCH {
        return vec![Event::Unsupported(FOREIGN_ABI.into())];
    }
    #[cfg(target_arch = "x86_64")]
    if n.data.nr as u32 & 0x4000_0000 != 0 {
        return vec![Event::Unsupported(FOREIGN_ABI.into())];
    }
    let m = Mem { pid: n.pid as i32 };
    let a = n.data.args;
    let ev = match n.data.nr as i64 {
        libc::SYS_openat => path(&m, a[0], a[1]).map(|path| Event::Open {
            path,
            flags: a[2] as i32,
        }),
        SYS_OPENAT2 => {
            let flags = m.read_u64(a[2]).ok();
            flags.and_then(|flags| {
                path(&m, a[0], a[1]).map(|path| Event::Open {
                    path,
                    flags: flags as i32,
                })
            })
        }
        libc::SYS_newfstatat => path(&m, a[0], a[1]).map(|path| Event::Stat {
            path,
            follow: follows(a[3]),
        }),
        libc::SYS_statx => path(&m, a[0], a[1]).map(|path| Event::Stat {
            path,
            follow: follows(a[2]),
        }),
        libc::SYS_faccessat => {
            path(&m, a[0], a[1]).map(|path| Event::Access { path, follow: true })
        }
        SYS_FACCESSAT2 => path(&m, a[0], a[1]).map(|path| Event::Access {
            path,
            follow: follows(a[3]),
        }),
        libc::SYS_readlinkat => path(&m, a[0], a[1]).map(|path| Event::Readlink { path }),
        libc::SYS_execve => path(&m, AT_FDCWD, a[0]).map(|path| Event::Exec { path }),
        libc::SYS_execveat => {
            let empty = m.read_cstr(a[1]).is_ok_and(|p| p.is_empty());
            let target = if empty && a[4] & libc::AT_EMPTY_PATH as u64 != 0 {
                m.fd_path(a[0] as i32)
            } else {
                path(&m, a[0], a[1])
            };
            target.map(|path| Event::Exec { path })
        }
        libc::SYS_getdents64 => m.fd_path(a[0] as i32).map(|path| Event::List { path }),
        libc::SYS_chdir => path(&m, AT_FDCWD, a[0]).map(|path| Event::Chdir { path }),
        libc::SYS_truncate => path(&m, AT_FDCWD, a[0]).map(|path| Event::Truncate {
            path,
            len: a[1] as i64,
        }),
        libc::SYS_renameat | libc::SYS_renameat2 => {
            match (path(&m, a[0], a[1]), path(&m, a[2], a[3])) {
                (Some(from), Some(to)) => Some(Event::Rename { from, to }),
                _ => None,
            }
        }
        libc::SYS_unlinkat => path(&m, a[0], a[1]).map(|path| Event::Remove { path }),
        libc::SYS_mkdirat | libc::SYS_mknodat => {
            path(&m, a[0], a[1]).map(|path| Event::Create { path })
        }
        libc::SYS_linkat => path(&m, a[2], a[3]).map(|path| Event::Create { path }),
        libc::SYS_symlinkat => path(&m, a[1], a[2]).map(|path| Event::Create { path }),
        libc::SYS_fchmodat | SYS_FCHMODAT2 | libc::SYS_fchownat | libc::SYS_utimensat => {
            path(&m, a[0], a[1]).map(|path| Event::SetAttr { path })
        }
        libc::SYS_connect => sockaddr(&m, a[1], a[2]).map(Event::Net),
        libc::SYS_bind => match sockaddr(&m, a[1], a[2]) {
            Some(NetTarget::Unix(p)) => Some(Event::Create {
                path: PathBuf::from(std::ffi::OsString::from_vec(p)),
            }),
            _ => None,
        },
        libc::SYS_sendto => sockaddr(&m, a[4], a[5]).map(Event::Net),
        libc::SYS_sendmsg => msg_dest(&m, a[1]).map(Event::Net),
        libc::SYS_sendmmsg => {
            let mut out = Vec::new();
            for i in 0..a[2].min(64) {
                if let Some(t) = msg_dest(&m, a[1] + i * 64) {
                    out.push(Event::Net(t));
                }
            }
            return out;
        }
        libc::SYS_read
        | libc::SYS_readv
        | libc::SYS_pread64
        | libc::SYS_preadv
        | libc::SYS_preadv2
        | libc::SYS_recvfrom
        | libc::SYS_recvmsg
        | libc::SYS_recvmmsg
        | libc::SYS_splice
        | libc::SYS_tee
        | libc::SYS_copy_file_range
        | libc::SYS_sendfile => stdin_read(&m, stdin_id),
        libc::SYS_open_by_handle_at => Some(Event::Unsupported(
            "opened a file by handle, which memo can't trace".into(),
        )),
        libc::SYS_mount
        | libc::SYS_umount2
        | libc::SYS_pivot_root
        | libc::SYS_chroot
        | libc::SYS_setns
        | SYS_OPEN_TREE
        | SYS_MOVE_MOUNT
        | SYS_FSOPEN
        | SYS_FSCONFIG
        | SYS_FSMOUNT
        | SYS_FSPICK
        | SYS_MOUNT_SETATTR => Some(Event::Unsupported(MOUNTS.into())),
        #[cfg(target_arch = "x86_64")]
        nr => decode_legacy(&m, nr, &a),
        #[cfg(not(target_arch = "x86_64"))]
        _ => None,
    };
    ev.into_iter().collect()
}

/// Decodes the path-based calls that only x86_64 still has.
#[cfg(target_arch = "x86_64")]
fn decode_legacy(m: &Mem, nr: i64, a: &[u64; 6]) -> Option<Event> {
    let p = |addr: u64| path(m, AT_FDCWD, addr);
    match nr {
        libc::SYS_open => p(a[0]).map(|path| Event::Open {
            path,
            flags: a[1] as i32,
        }),
        libc::SYS_creat => p(a[0]).map(|path| Event::Open {
            path,
            flags: libc::O_CREAT | libc::O_WRONLY | libc::O_TRUNC,
        }),
        libc::SYS_stat => p(a[0]).map(|path| Event::Stat { path, follow: true }),
        libc::SYS_lstat => p(a[0]).map(|path| Event::Stat {
            path,
            follow: false,
        }),
        libc::SYS_access => p(a[0]).map(|path| Event::Access { path, follow: true }),
        libc::SYS_readlink => p(a[0]).map(|path| Event::Readlink { path }),
        libc::SYS_getdents => m.fd_path(a[0] as i32).map(|path| Event::List { path }),
        libc::SYS_rename => match (p(a[0]), p(a[1])) {
            (Some(from), Some(to)) => Some(Event::Rename { from, to }),
            _ => None,
        },
        libc::SYS_unlink | libc::SYS_rmdir => p(a[0]).map(|path| Event::Remove { path }),
        libc::SYS_mkdir | libc::SYS_mknod => p(a[0]).map(|path| Event::Create { path }),
        libc::SYS_link | libc::SYS_symlink => p(a[1]).map(|path| Event::Create { path }),
        libc::SYS_chmod
        | libc::SYS_chown
        | libc::SYS_lchown
        | libc::SYS_utime
        | libc::SYS_utimes => p(a[0]).map(|path| Event::SetAttr { path }),
        libc::SYS_futimesat => path(m, a[0], a[1]).map(|path| Event::SetAttr { path }),
        _ => None,
    }
}
