//! Postal addresses as the lines printed on an envelope.

use crate::error::Error;

/// Maximum address lines drawn on the envelope. Extra lines are dropped.
pub const MAX_LINES: usize = 6;

/// An address as a stack of print lines.
#[derive(Debug, Clone, PartialEq, Eq)]
pub struct Address {
    lines: Vec<String>,
}

impl Address {
    /// Parse a freeform block. Blank lines are dropped. Extra lines beyond
    /// [`MAX_LINES`] are dropped.
    pub fn parse(text: &str) -> Result<Self, Error> {
        Self::parse_named("address", text)
    }

    /// Like [`parse`], but names the field in empty-input errors (`from` / `to`).
    pub fn parse_named(which: &'static str, text: &str) -> Result<Self, Error> {
        let mut lines: Vec<String> = text
            .lines()
            .map(str::trim)
            .filter(|line| !line.is_empty())
            .map(ToString::to_string)
            .collect();
        if lines.is_empty() {
            let collapsed = text.split_whitespace().collect::<Vec<_>>().join(" ");
            if collapsed.is_empty() {
                return Err(Error::EmptyAddress(which));
            }
            lines.push(collapsed);
        }
        lines.truncate(MAX_LINES);
        Ok(Address { lines })
    }

    /// Lines printed on the envelope, in order.
    pub fn lines(&self) -> &[String] {
        &self.lines
    }

    /// Single-line query sent to the Geocoding API.
    pub fn geocode_query(&self) -> String {
        self.lines.join(", ")
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn parse_drops_blank_lines() {
        let addr = Address::parse("Ada Lovelace\n\n12 St James's Square\nLondon").unwrap();
        assert_eq!(
            addr.lines(),
            ["Ada Lovelace", "12 St James's Square", "London"]
        );
    }

    #[test]
    fn parse_rejects_empty() {
        assert!(matches!(
            Address::parse_named("from", "  \n\t"),
            Err(Error::EmptyAddress("from"))
        ));
    }

    #[test]
    fn parse_caps_lines() {
        let block = (0..10)
            .map(|i| format!("line {i}"))
            .collect::<Vec<_>>()
            .join("\n");
        let addr = Address::parse(&block).unwrap();
        assert_eq!(addr.lines().len(), MAX_LINES);
    }
}
