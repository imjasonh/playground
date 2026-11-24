use clap::parser::ValueSource;
use clap::{ArgMatches, Command};

/// Returns the parts of a ping for a program parsed with clap: the names of the
/// subcommands the user ran, then the names of the flags they set, sorted.
///
/// A flag is named by its long name, then its short name, then its id. This
/// leaves out positional arguments and every value, and it leaves out an
/// argument that only has a default.
///
/// `cmd` must be the command that produced `matches`.
pub(crate) fn clap_parts(cmd: &Command, matches: &ArgMatches) -> Vec<String> {
    let mut subcommands = Vec::new();
    let mut flags = Vec::new();
    let mut cmd = cmd;
    let mut matches = matches;
    loop {
        for arg in cmd.get_arguments().filter(|a| !a.is_positional()) {
            let id = arg.get_id().as_str();
            let set = matches.try_contains_id(id).unwrap_or(false)
                && matches.value_source(id) == Some(ValueSource::CommandLine);
            if set {
                flags.push(flag_name(arg));
            }
        }
        let Some((name, sub_matches)) = matches.subcommand() else {
            break;
        };
        let Some(sub_cmd) = cmd.find_subcommand(name) else {
            break;
        };
        subcommands.push(name.to_owned());
        cmd = sub_cmd;
        matches = sub_matches;
    }
    flags.sort();
    flags.dedup();
    subcommands.extend(flags);
    subcommands
}

fn flag_name(arg: &clap::Arg) -> String {
    if let Some(long) = arg.get_long() {
        return long.to_owned();
    }
    if let Some(short) = arg.get_short() {
        return short.to_string();
    }
    arg.get_id().to_string()
}

#[cfg(test)]
mod tests {
    use super::*;
    use clap::{Arg, ArgAction};

    fn command() -> Command {
        Command::new("tool")
            .arg(
                Arg::new("verbose")
                    .long("verbose")
                    .action(ArgAction::SetTrue),
            )
            .arg(Arg::new("file").help("positional"))
            .subcommand(
                Command::new("sim")
                    .arg(Arg::new("games").long("games").default_value("200"))
                    .arg(Arg::new("seed").long("seed"))
                    .arg(Arg::new("out").short('o'))
                    .arg(Arg::new("json").long("json").action(ArgAction::SetTrue))
                    .arg(Arg::new("target")),
            )
    }

    fn parts(args: &[&str]) -> Vec<String> {
        let cmd = command();
        let matches = cmd.clone().try_get_matches_from(args).unwrap();
        clap_parts(&cmd, &matches)
    }

    #[test]
    fn names_subcommands_then_sorted_flags() {
        assert_eq!(
            parts(&[
                "tool",
                "--verbose",
                "sim",
                "--seed",
                "secret",
                "--json",
                "-o",
                "x"
            ]),
            ["sim", "json", "o", "seed", "verbose"]
        );
    }

    #[test]
    fn leaves_out_values_positionals_and_defaults() {
        assert_eq!(parts(&["tool", "private/path"]), Vec::<String>::new());
        assert_eq!(parts(&["tool", "sim", "/etc/passwd"]), ["sim"]);
    }

    #[test]
    fn counts_a_flag_given_its_default() {
        assert_eq!(parts(&["tool", "sim", "--games", "200"]), ["sim", "games"]);
    }
}
