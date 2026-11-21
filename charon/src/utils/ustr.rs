//! Interned strings.
use rustc_hash::FxHashMap;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::sync::{LazyLock, Mutex};

/// An interned string: cheap to copy, compare and hash. Interned strings are never freed.
///
/// This points to the interned `&str` so that it's only one pointer wide.
#[derive(Clone, Copy)]
#[cfg_attr(feature = "charon_on_charon", charon::opaque)]
pub struct Ustr(&'static &'static str);

static INTERNED: LazyLock<Mutex<FxHashMap<&'static str, &'static &'static str>>> =
    LazyLock::new(Default::default);

impl Ustr {
    pub fn as_str(&self) -> &'static str {
        *self.0
    }
}

impl From<&str> for Ustr {
    fn from(s: &str) -> Self {
        let mut interned = INTERNED.lock().unwrap();
        if let Some(&s) = interned.get(s) {
            return Ustr(s);
        }
        let s: &'static str = Box::leak(s.into());
        let interned_s = Box::leak(Box::new(s));
        interned.insert(s, interned_s);
        Ustr(interned_s)
    }
}

impl Default for Ustr {
    fn default() -> Self {
        Ustr::from("")
    }
}

impl From<String> for Ustr {
    fn from(s: String) -> Self {
        Ustr::from(s.as_str())
    }
}

// Interning makes equal strings share their address.
impl PartialEq for Ustr {
    fn eq(&self, other: &Self) -> bool {
        std::ptr::eq(self.0, other.0)
    }
}
impl Eq for Ustr {}

impl Hash for Ustr {
    fn hash<H: Hasher>(&self, state: &mut H) {
        std::ptr::hash(self.0, state)
    }
}

impl PartialOrd for Ustr {
    fn partial_cmp(&self, other: &Self) -> Option<std::cmp::Ordering> {
        Some(self.cmp(other))
    }
}
impl Ord for Ustr {
    fn cmp(&self, other: &Self) -> std::cmp::Ordering {
        self.0.cmp(other.0)
    }
}

impl Deref for Ustr {
    type Target = str;
    fn deref(&self) -> &str {
        self.0
    }
}

impl fmt::Display for Ustr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.0, f)
    }
}
impl fmt::Debug for Ustr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.0, f)
    }
}

impl Serialize for Ustr {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(self.0)
    }
}
impl<'de> Deserialize<'de> for Ustr {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        Ok(Ustr::from(String::deserialize(deserializer)?))
    }
}
