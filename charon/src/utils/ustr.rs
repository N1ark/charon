//! Interned strings.
use rustc_hash::FxHashSet;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use std::fmt;
use std::hash::{Hash, Hasher};
use std::ops::Deref;
use std::sync::{LazyLock, Mutex};

/// An interned string: cheap to copy, compare and hash. Interned strings are never freed.
#[derive(Clone, Copy)]
#[cfg_attr(feature = "charon_on_charon", charon::opaque)]
pub struct Ustr(&'static str);

static INTERNED: LazyLock<Mutex<FxHashSet<&'static str>>> = LazyLock::new(Default::default);

impl Ustr {
    pub fn as_str(&self) -> &'static str {
        self.0
    }
}

impl From<&str> for Ustr {
    fn from(s: &str) -> Self {
        let mut interned = INTERNED.lock().unwrap();
        if let Some(s) = interned.get(s) {
            return Ustr(s);
        }
        let s: &'static str = Box::leak(s.into());
        interned.insert(s);
        Ustr(s)
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
        self.0.as_ptr().hash(state)
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
