use std::{
    io::{ErrorKind, Read, Write},
    net::{Shutdown, TcpStream, ToSocketAddrs},
    time::{Duration, Instant},
};

use anyhow::{Context, Result, anyhow, bail};
use sunset::{
    ChanData, ChanHandle, CliEvent, Client, Error as SunsetError, Event, Pty, PubKey, Runner,
    SignKey,
};

use esp32_eink::terminal::{COLS, ROWS, TerminalBuffer};

use crate::ssh_config::{SshConfig, host_key_fingerprint};

const CONNECT_TIMEOUT: Duration = Duration::from_secs(10);
const SESSION_TIMEOUT: Duration = Duration::from_secs(30);
const PACKET_BUFFER: usize = 4096;
const NETWORK_BUFFER: usize = 4096;
const CHANNEL_BUFFER: usize = 1024;

enum ProgressAction {
    None,
    OpenSession,
    Defunct,
}

pub fn connect_display_disconnect(
    cfg: &SshConfig,
    key: &SignKey,
    terminal: &mut TerminalBuffer,
) -> Result<()> {
    terminal.write_line(&format!("Connecting to {}:{}...", cfg.host, cfg.port));
    let mut socket = connect(&cfg.host, cfg.port)?;
    socket
        .set_nonblocking(true)
        .context("set SSH socket nonblocking")?;
    socket.set_nodelay(true).context("set SSH TCP_NODELAY")?;

    let mut input_packets = [0_u8; PACKET_BUFFER];
    let mut output_packets = [0_u8; PACKET_BUFFER];
    let mut runner = Runner::<Client>::new_client(&mut input_packets, &mut output_packets);

    let mut network = [0_u8; NETWORK_BUFFER];
    let mut network_start = 0;
    let mut network_end = 0;
    let mut socket_eof = false;
    let mut channel: Option<ChanHandle> = None;
    let mut shell_open = false;
    let command = format!("{}\r\nexit\r\n", cfg.command);
    let mut command_offset = 0;
    let mut authenticated = false;
    let mut exit_status = None;
    let deadline = Instant::now() + SESSION_TIMEOUT;

    while Instant::now() < deadline {
        let mut did_work = false;

        // Flush SSH packets before accepting more input. Sunset deliberately
        // back-pressures input during key exchange when its output is pending.
        loop {
            let write_result = {
                let pending = runner.output_buf();
                if pending.is_empty() {
                    break;
                }
                socket.write(pending)
            };
            match write_result {
                Ok(0) => bail!("SSH socket closed while sending"),
                Ok(written) => {
                    runner.consume_output(written);
                    did_work = true;
                }
                Err(error) if error.kind() == ErrorKind::WouldBlock => break,
                Err(error) if error.kind() == ErrorKind::Interrupted => continue,
                Err(error) => return Err(error).context("write SSH socket"),
            }
        }

        // Feed any bytes retained from a partial Runner::input() call.
        if network_start < network_end && runner.is_input_ready() {
            let consumed = runner
                .input(&network[network_start..network_end])
                .map_err(|error| anyhow!("parse SSH packet: {error}"))?;
            network_start += consumed;
            did_work |= consumed > 0;
            if network_start == network_end {
                network_start = 0;
                network_end = 0;
            }
        }

        if !socket_eof && network_start == network_end && runner.is_input_ready() {
            match socket.read(&mut network) {
                Ok(0) => {
                    socket_eof = true;
                    runner.close_input();
                    did_work = true;
                }
                Ok(read) => {
                    network_start = 0;
                    network_end = read;
                    did_work = true;
                }
                Err(error) if error.kind() == ErrorKind::WouldBlock => {}
                Err(error) if error.kind() == ErrorKind::Interrupted => {}
                Err(error) => return Err(error).context("read SSH socket"),
            }
        }

        let action = {
            let event = runner
                .progress()
                .map_err(|error| anyhow!("advance SSH session: {error}"))?;
            match event {
                Event::Cli(CliEvent::Hostkey(hostkey)) => {
                    let received = hostkey
                        .hostkey()
                        .map_err(|error| anyhow!("read SSH host key: {error}"))?;
                    let (matches, received_fingerprint) = match &received {
                        PubKey::Ed25519(received) => (
                            received.key.0 == cfg.host_key,
                            host_key_fingerprint(&received.key.0),
                        ),
                        _ => (false, "unsupported key type".to_string()),
                    };
                    if matches {
                        hostkey
                            .accept()
                            .map_err(|error| anyhow!("accept SSH host key: {error}"))?;
                        ProgressAction::None
                    } else {
                        hostkey
                            .reject()
                            .map_err(|error| anyhow!("reject SSH host key: {error}"))?;
                        bail!(
                            "SSH host key mismatch (received {received_fingerprint}, expected {})",
                            host_key_fingerprint(&cfg.host_key)
                        );
                    }
                }
                Event::Cli(CliEvent::Username(username)) => {
                    username
                        .username(&cfg.username)
                        .map_err(|error| anyhow!("provide SSH username: {error}"))?;
                    ProgressAction::None
                }
                Event::Cli(CliEvent::Password(password)) => {
                    password
                        .skip()
                        .map_err(|error| anyhow!("skip SSH password auth: {error}"))?;
                    ProgressAction::None
                }
                Event::Cli(CliEvent::Pubkey(pubkey)) => {
                    pubkey
                        .pubkey(key.clone())
                        .map_err(|error| anyhow!("provide SSH client key: {error}"))?;
                    ProgressAction::None
                }
                Event::Cli(CliEvent::AgentSign(agent)) => {
                    agent
                        .skip()
                        .map_err(|error| anyhow!("skip SSH agent auth: {error}"))?;
                    ProgressAction::None
                }
                Event::Cli(CliEvent::Authenticated) => {
                    authenticated = true;
                    ProgressAction::OpenSession
                }
                Event::Cli(CliEvent::SessionOpened(mut opener)) => {
                    let pty = Pty {
                        term: "xterm"
                            .try_into()
                            .map_err(|_| anyhow!("xterm PTY name is too long"))?,
                        cols: COLS as u32,
                        rows: ROWS as u32,
                        width: 0,
                        height: 0,
                        modes: Default::default(),
                    };
                    opener
                        .pty(pty)
                        .map_err(|error| anyhow!("request 80x25 PTY: {error}"))?;
                    opener
                        .shell()
                        .map_err(|error| anyhow!("request SSH shell: {error}"))?;
                    shell_open = true;
                    terminal.clear();
                    ProgressAction::None
                }
                Event::Cli(CliEvent::SessionExit(exit)) => {
                    if let sunset::CliSessionExit::Status(status) = exit {
                        exit_status = Some(status);
                    }
                    ProgressAction::None
                }
                Event::Cli(CliEvent::Banner(banner)) => {
                    if let Ok(text) = banner.banner() {
                        terminal.feed(text.as_bytes());
                        terminal.feed(b"\r\n");
                    }
                    ProgressAction::None
                }
                Event::Cli(CliEvent::Defunct) => ProgressAction::Defunct,
                Event::Cli(CliEvent::PollAgain) | Event::Progressed => {
                    did_work = true;
                    ProgressAction::None
                }
                Event::None => ProgressAction::None,
                Event::Serv(_) => return Err(anyhow!("client Runner emitted a server event")),
            }
        };

        match action {
            ProgressAction::OpenSession => {
                channel = Some(
                    runner
                        .open_client_session()
                        .map_err(|error| anyhow!("open SSH session channel: {error}"))?,
                );
                did_work = true;
            }
            ProgressAction::Defunct => {
                channel = None;
                break;
            }
            ProgressAction::None => {}
        }

        if let Some(active_channel) = channel.as_ref() {
            let mut output = [0_u8; CHANNEL_BUFFER];
            loop {
                match runner.read_channel(active_channel, ChanData::Normal, &mut output) {
                    Ok(0) => break,
                    Ok(read) => {
                        terminal.feed(&output[..read]);
                        did_work = true;
                    }
                    Err(SunsetError::ChannelEOF) => break,
                    Err(error) => return Err(anyhow!("read SSH channel: {error}")),
                }
            }

            if shell_open && command_offset < command.len() {
                match runner.write_channel(
                    active_channel,
                    ChanData::Normal,
                    &command.as_bytes()[command_offset..],
                ) {
                    Ok(written) => {
                        command_offset += written;
                        did_work |= written > 0;
                    }
                    Err(SunsetError::ChannelEOF) => {}
                    Err(error) => return Err(anyhow!("write SSH command: {error}")),
                }
            }

            if runner.is_channel_closed(active_channel) {
                let channel = channel.take().expect("channel existed");
                runner
                    .channel_done(channel)
                    .map_err(|error| anyhow!("release SSH channel: {error}"))?;
                break;
            }
        }

        if !did_work {
            std::thread::sleep(Duration::from_millis(10));
        }
    }

    let _ = socket.shutdown(Shutdown::Both);
    if !authenticated {
        bail!("SSH authentication did not complete");
    }
    if channel.is_some() {
        bail!(
            "SSH session timed out after {} seconds",
            SESSION_TIMEOUT.as_secs()
        );
    }
    if let Some(status) = exit_status {
        tracing::info!(status, "ssh: remote command exited");
    }
    Ok(())
}

fn connect(host: &str, port: u16) -> Result<TcpStream> {
    let addresses = (host, port)
        .to_socket_addrs()
        .with_context(|| format!("resolve {host}:{port}"))?;
    let mut last_error = None;
    for address in addresses {
        match TcpStream::connect_timeout(&address, CONNECT_TIMEOUT) {
            Ok(socket) => return Ok(socket),
            Err(error) => last_error = Some(error),
        }
    }
    Err(last_error
        .map(anyhow::Error::from)
        .unwrap_or_else(|| anyhow!("DNS returned no addresses for {host}:{port}")))
    .with_context(|| format!("connect to {host}:{port}"))
}
