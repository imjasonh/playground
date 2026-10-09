//! Reads arguments out of a blocked tracee: strings and structs from its
//! memory, and its working directory and open files from `/proc`.

use std::ffi::OsStr;
use std::fs;
use std::io;
use std::os::unix::ffi::{OsStrExt, OsStringExt};
use std::path::PathBuf;

const PATH_MAX: usize = 4096;
const CHUNK: usize = 4096;

pub struct Mem {
    pub pid: i32,
}

impl Mem {
    /// Fills `buf` from the tracee's memory at `addr`. Reads never cross a
    /// 4 KiB boundary in one call, so a mapped prefix is read even when the
    /// next page isn't mapped.
    pub fn read(&self, mut addr: u64, buf: &mut [u8]) -> io::Result<usize> {
        let mut done = 0;
        while done < buf.len() {
            let room = CHUNK - (addr as usize % CHUNK);
            let want = room.min(buf.len() - done);
            let local = libc::iovec {
                iov_base: buf[done..].as_mut_ptr().cast(),
                iov_len: want,
            };
            let remote = libc::iovec {
                iov_base: addr as *mut libc::c_void,
                iov_len: want,
            };
            // SAFETY: both iovecs describe valid memory: `local` points into
            // `buf` with `want` bytes left, and the kernel validates `remote`.
            let n = unsafe { libc::process_vm_readv(self.pid, &local, 1, &remote, 1, 0) };
            if n < 0 {
                if done > 0 {
                    break;
                }
                return Err(io::Error::last_os_error());
            }
            let n = n as usize;
            done += n;
            addr += n as u64;
            if n < want {
                break;
            }
        }
        Ok(done)
    }

    pub fn read_exact(&self, addr: u64, buf: &mut [u8]) -> io::Result<()> {
        if self.read(addr, buf)? == buf.len() {
            Ok(())
        } else {
            Err(io::Error::from_raw_os_error(libc::EFAULT))
        }
    }

    pub fn read_u64(&self, addr: u64) -> io::Result<u64> {
        let mut b = [0u8; 8];
        self.read_exact(addr, &mut b)?;
        Ok(u64::from_ne_bytes(b))
    }

    pub fn read_u32(&self, addr: u64) -> io::Result<u32> {
        let mut b = [0u8; 4];
        self.read_exact(addr, &mut b)?;
        Ok(u32::from_ne_bytes(b))
    }

    /// Reads a NUL-terminated string of at most `PATH_MAX` bytes.
    pub fn read_cstr(&self, addr: u64) -> io::Result<Vec<u8>> {
        if addr == 0 {
            return Err(io::Error::from_raw_os_error(libc::EFAULT));
        }
        let mut out = Vec::new();
        let mut buf = [0u8; CHUNK];
        let mut at = addr;
        while out.len() < PATH_MAX {
            let room = CHUNK - (at as usize % CHUNK);
            let n = self.read(at, &mut buf[..room])?;
            if n == 0 {
                return Err(io::Error::from_raw_os_error(libc::EFAULT));
            }
            if let Some(end) = buf[..n].iter().position(|&c| c == 0) {
                out.extend_from_slice(&buf[..end]);
                return Ok(out);
            }
            out.extend_from_slice(&buf[..n]);
            at += n as u64;
        }
        Err(io::Error::from_raw_os_error(libc::ENAMETOOLONG))
    }

    fn proc_link(&self, what: &str) -> Option<Vec<u8>> {
        let target = fs::read_link(format!("/proc/{}/{what}", self.pid)).ok()?;
        let target = target.into_os_string().into_vec();
        if target.first() != Some(&b'/') || target.ends_with(b" (deleted)") {
            return None;
        }
        Some(target)
    }

    /// Returns the path of file descriptor `fd`, if it refers to a file or
    /// directory that still exists.
    pub fn fd_path(&self, fd: i32) -> Option<PathBuf> {
        self.proc_link(&format!("fd/{fd}")).map(|p| normalize(&p))
    }

    /// Resolves a path argument the way the kernel does for `*at` calls:
    /// relative to `dirfd`, or to the working directory for `AT_FDCWD`.
    pub fn resolve(&self, dirfd: i32, raw: &[u8]) -> Option<PathBuf> {
        if raw.first() == Some(&b'/') {
            return Some(normalize(raw));
        }
        let mut base = if dirfd == libc::AT_FDCWD {
            self.proc_link("cwd")?
        } else {
            self.proc_link(&format!("fd/{dirfd}"))?
        };
        base.push(b'/');
        base.extend_from_slice(raw);
        Some(normalize(&base))
    }
}

/// Drops empty and `.` components and a trailing slash. `..` stays, since
/// collapsing it would be wrong after a symlink.
pub fn normalize(raw: &[u8]) -> PathBuf {
    let mut out = Vec::with_capacity(raw.len() + 1);
    for part in raw.split(|&c| c == b'/') {
        if part.is_empty() || part == b"." {
            continue;
        }
        out.push(b'/');
        out.extend_from_slice(part);
    }
    if out.is_empty() {
        out.push(b'/');
    }
    PathBuf::from(OsStr::from_bytes(&out))
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn normalizes() {
        assert_eq!(normalize(b"/a//b/./c/"), PathBuf::from("/a/b/c"));
        assert_eq!(normalize(b"/a/../b"), PathBuf::from("/a/../b"));
        assert_eq!(normalize(b"/"), PathBuf::from("/"));
        assert_eq!(normalize(b"//"), PathBuf::from("/"));
    }

    #[test]
    fn reads_own_memory() {
        let m = Mem {
            pid: std::process::id() as i32,
        };
        let s = b"hello\0world";
        assert_eq!(m.read_cstr(s.as_ptr() as u64).unwrap(), b"hello");
        let n: u64 = 0x1122_3344_5566_7788;
        assert_eq!(m.read_u64(&n as *const u64 as u64).unwrap(), n);
        assert!(m.read_cstr(0).is_err());
        let cwd = std::env::current_dir().unwrap();
        assert_eq!(m.resolve(libc::AT_FDCWD, b"x/./y"), Some(cwd.join("x/y")));
    }
}
