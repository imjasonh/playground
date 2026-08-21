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

    /// Delivery addresses bold the first line when it has no digits.
    pub fn first_line_is_name(&self) -> bool {
        match self.lines.first() {
            Some(line) => !has_digit(line),
            None => false,
        }
    }

    /// Keep leading name lines and replace the rest with Geocoding print
    /// lines. Empty `postal_lines` leaves the original address.
    pub fn expand_with(&self, postal_lines: &[String]) -> Address {
        let postal: Vec<String> = postal_lines
            .iter()
            .map(|s| s.trim())
            .filter(|s| !s.is_empty())
            .map(ToString::to_string)
            .collect();
        if postal.is_empty() {
            return self.clone();
        }
        let mut lines = self.leading_names();
        lines.extend(postal);
        lines.truncate(MAX_LINES);
        Address { lines }
    }

    /// Lines before the first digit, or every line but the last when
    /// nothing looks like a street number.
    fn leading_names(&self) -> Vec<String> {
        if self.lines.iter().any(|line| has_digit(line)) {
            return self
                .lines
                .iter()
                .take_while(|line| !has_digit(line))
                .cloned()
                .collect();
        }
        if self.lines.len() >= 2 {
            return self.lines[..self.lines.len() - 1].to_vec();
        }
        Vec::new()
    }
}

fn has_digit(s: &str) -> bool {
    s.chars().any(|c| c.is_ascii_digit())
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

    #[test]
    fn expand_short_street_keeps_no_name() {
        let addr = Address::parse("123 fake st\nbrooklyn").unwrap();
        let expanded = addr.expand_with(&["123 Fake St".into(), "Brooklyn, NY 11231".into()]);
        assert_eq!(expanded.lines(), ["123 Fake St", "Brooklyn, NY 11231"]);
        assert!(!expanded.first_line_is_name());
    }

    #[test]
    fn expand_keeps_recipient_name() {
        let addr = Address::parse("Ada Example\n1600 Amphitheatre Parkway\nMountain View").unwrap();
        let expanded = addr.expand_with(&[
            "1600 Amphitheatre Pkwy".into(),
            "Mountain View, CA 94043".into(),
        ]);
        assert_eq!(
            expanded.lines(),
            [
                "Ada Example",
                "1600 Amphitheatre Pkwy",
                "Mountain View, CA 94043"
            ]
        );
        assert!(expanded.first_line_is_name());
    }

    #[test]
    fn expand_empty_postal_keeps_original() {
        let addr = Address::parse("123 fake st\nbrooklyn").unwrap();
        assert_eq!(addr.expand_with(&[]).lines(), addr.lines());
    }
}
