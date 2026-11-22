//! Interned strings.
use crate::utils::dedup::*;
use serde::{Deserialize, Deserializer, Serialize, Serializer};
use serde_state::{DeserializeState, SerializeState};
use std::fmt;
use std::ops::Deref;

/// An interned string: cheap to copy, compare and hash. Like hash-consed values, interned strings
/// are deduplicated in the serialized output: see [`crate::utils::dedup`].
#[derive(Clone, Copy, Default, PartialEq, Eq, PartialOrd, Ord, Hash)]
#[cfg_attr(feature = "charon_on_charon", charon::opaque)]
pub struct Ustr(ustr::Ustr);

impl Ustr {
    pub fn as_str(&self) -> &'static str {
        self.0.as_str()
    }
}

impl From<&str> for Ustr {
    fn from(s: &str) -> Self {
        Ustr(ustr::Ustr::from(s))
    }
}

impl From<String> for Ustr {
    fn from(s: String) -> Self {
        Ustr::from(s.as_str())
    }
}

impl Deref for Ustr {
    type Target = str;
    fn deref(&self) -> &str {
        self.as_str()
    }
}

impl fmt::Display for Ustr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Display::fmt(self.as_str(), f)
    }
}

impl fmt::Debug for Ustr {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        fmt::Debug::fmt(self.as_str(), f)
    }
}

impl Serialize for Ustr {
    fn serialize<S: Serializer>(&self, serializer: S) -> Result<S::Ok, S::Error> {
        SerDedup::Untagged(self.as_str()).serialize(serializer)
    }
}

impl<State: DedupSerializerState> SerializeState<State> for Ustr {
    fn serialize_state<S: Serializer>(
        &self,
        state: &State,
        serializer: S,
    ) -> Result<S::Ok, S::Error> {
        serialize_dedup(self, || self.as_str().to_owned(), state, serializer)
    }
}

impl<'de> Deserialize<'de> for Ustr {
    fn deserialize<D: Deserializer<'de>>(deserializer: D) -> Result<Self, D::Error> {
        use serde::de::Error;
        match SerDedup::<String>::deserialize(deserializer)? {
            SerDedup::Untagged(s) => Ok(Ustr::from(s)),
            SerDedup::Value(..) | SerDedup::Deduplicated(..) => {
                Err(D::Error::custom(stateless_deserialize_error::<Ustr>()))
            }
        }
    }
}

impl<'de, State: DedupSerializerState> DeserializeState<'de, State> for Ustr {
    fn deserialize_state<D: Deserializer<'de>>(
        state: &State,
        deserializer: D,
    ) -> Result<Self, D::Error> {
        deserialize_dedup(state, deserializer, |s: String| Ustr::from(s))
    }
}
