pub mod legacy {
    #[deprecated(note = "use new_fn instead")]
    pub fn old_fn() -> i32 { 1 }

    pub fn new_fn() -> i32 { 2 }
}

pub struct Client;

impl Client {
    #[deprecated]
    pub fn post(&self) -> i32 { 3 }

    pub fn send(&self) -> i32 { 4 }
}
