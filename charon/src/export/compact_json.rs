//! A JSON serializer that writes structs as arrays of their field values (in declaration order)
//! instead of objects keyed by field names. Everything else is written the way `serde_json`
//! writes it.
use serde::ser::{self, Serialize};
use std::fmt::Display;
use std::io::{self, Write};

#[derive(Debug)]
pub struct Error(String);

impl Display for Error {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        f.write_str(&self.0)
    }
}
impl std::error::Error for Error {}
impl ser::Error for Error {
    fn custom<T: Display>(msg: T) -> Self {
        Error(msg.to_string())
    }
}
impl From<io::Error> for Error {
    fn from(err: io::Error) -> Self {
        Error(err.to_string())
    }
}

/// We write to this buffer, and hand it to the writer once it exceeds this size.
const FLUSH_THRESHOLD: usize = 1 << 16;

pub struct Serializer<W: Write> {
    buf: Vec<u8>,
    writer: W,
}

impl<W: Write> Serializer<W> {
    pub fn new(writer: W) -> Self {
        Serializer {
            buf: Vec::with_capacity(2 * FLUSH_THRESHOLD),
            writer,
        }
    }

    /// Write out the remaining buffered output.
    pub fn finish(mut self) -> Result<W, Error> {
        self.writer.write_all(&self.buf)?;
        self.writer.flush()?;
        Ok(self.writer)
    }

    fn maybe_flush(&mut self) -> Result<(), Error> {
        if self.buf.len() >= FLUSH_THRESHOLD {
            self.writer.write_all(&self.buf)?;
            self.buf.clear();
        }
        Ok(())
    }

    fn write_int(&mut self, i: impl itoa::Integer) {
        self.buf
            .extend_from_slice(itoa::Buffer::new().format(i).as_bytes());
    }

    fn write_u64(&mut self, i: u64) {
        // Most of our integers are small ids.
        if i < 10 {
            self.buf.push(b'0' + i as u8);
        } else if i < 100 {
            self.buf
                .extend_from_slice(&[b'0' + (i / 10) as u8, b'0' + (i % 10) as u8]);
        } else {
            self.write_int(i);
        }
    }

    /// Write a string that we know doesn't need escaping, e.g. a variant name.
    fn write_ident(&mut self, s: &str) {
        self.buf.push(b'"');
        self.buf.extend_from_slice(s.as_bytes());
        self.buf.push(b'"');
    }

    fn write_str(&mut self, s: &str) {
        let buf = &mut self.buf;
        buf.push(b'"');
        let bytes = s.as_bytes();
        let mut start = 0;
        for (i, &byte) in bytes.iter().enumerate() {
            let escape = ESCAPE[byte as usize];
            if escape == 0 {
                continue;
            }
            buf.extend_from_slice(&bytes[start..i]);
            if escape == b'u' {
                const HEX_DIGITS: &[u8; 16] = b"0123456789abcdef";
                buf.extend_from_slice(&[
                    b'\\',
                    b'u',
                    b'0',
                    b'0',
                    HEX_DIGITS[(byte >> 4) as usize],
                    HEX_DIGITS[(byte & 0xF) as usize],
                ]);
            } else {
                buf.extend_from_slice(&[b'\\', escape]);
            }
            start = i + 1;
        }
        buf.extend_from_slice(&bytes[start..]);
        buf.push(b'"');
    }

    /// Start the `{"variant":` wrapper that `serde_json` uses for non-unit enum variants.
    fn begin_variant(&mut self, variant: &str) {
        self.buf.push(b'{');
        self.write_ident(variant);
        self.buf.push(b':');
    }
}

// What to write after a backslash to escape the given byte, or 0 if it doesn't need escaping.
// `u` means `\u00XX`.
const ESCAPE: [u8; 256] = {
    let mut table = [0; 256];
    let mut i = 0;
    while i < 0x20 {
        table[i] = b'u';
        i += 1;
    }
    table[0x08] = b'b';
    table[0x09] = b't';
    table[0x0A] = b'n';
    table[0x0C] = b'f';
    table[0x0D] = b'r';
    table[b'"' as usize] = b'"';
    table[b'\\' as usize] = b'\\';
    table
};

/// A sequence-like value being serialized. `close` is what we write at the end.
pub struct Compound<'a, W: Write> {
    ser: &'a mut Serializer<W>,
    first: bool,
    close: &'static [u8],
}

impl<'a, W: Write> Compound<'a, W> {
    fn new(ser: &'a mut Serializer<W>, open: &[u8], close: &'static [u8]) -> Self {
        ser.buf.extend_from_slice(open);
        Compound {
            ser,
            first: true,
            close,
        }
    }

    fn element<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        if !self.first {
            self.ser.buf.push(b',');
        }
        self.first = false;
        value.serialize(&mut *self.ser)?;
        self.ser.maybe_flush()
    }

    fn end(self) -> Result<(), Error> {
        self.ser.buf.extend_from_slice(self.close);
        Ok(())
    }
}

impl<'a, W: Write> ser::Serializer for &'a mut Serializer<W> {
    type Ok = ();
    type Error = Error;
    type SerializeSeq = Compound<'a, W>;
    type SerializeTuple = Compound<'a, W>;
    type SerializeTupleStruct = Compound<'a, W>;
    type SerializeTupleVariant = Compound<'a, W>;
    type SerializeMap = Compound<'a, W>;
    type SerializeStruct = Compound<'a, W>;
    type SerializeStructVariant = Compound<'a, W>;

    fn serialize_bool(self, v: bool) -> Result<(), Error> {
        self.buf
            .extend_from_slice(if v { b"true" } else { b"false" });
        Ok(())
    }
    fn serialize_i8(self, v: i8) -> Result<(), Error> {
        self.write_int(v);
        Ok(())
    }
    fn serialize_i16(self, v: i16) -> Result<(), Error> {
        self.write_int(v);
        Ok(())
    }
    fn serialize_i32(self, v: i32) -> Result<(), Error> {
        self.write_int(v);
        Ok(())
    }
    fn serialize_i64(self, v: i64) -> Result<(), Error> {
        self.write_int(v);
        Ok(())
    }
    fn serialize_i128(self, v: i128) -> Result<(), Error> {
        self.write_int(v);
        Ok(())
    }
    fn serialize_u8(self, v: u8) -> Result<(), Error> {
        self.write_u64(v.into());
        Ok(())
    }
    fn serialize_u16(self, v: u16) -> Result<(), Error> {
        self.write_u64(v.into());
        Ok(())
    }
    fn serialize_u32(self, v: u32) -> Result<(), Error> {
        self.write_u64(v.into());
        Ok(())
    }
    fn serialize_u64(self, v: u64) -> Result<(), Error> {
        self.write_u64(v);
        Ok(())
    }
    fn serialize_u128(self, v: u128) -> Result<(), Error> {
        self.write_int(v);
        Ok(())
    }
    fn serialize_f32(self, v: f32) -> Result<(), Error> {
        if v.is_finite() {
            self.buf
                .extend_from_slice(ryu::Buffer::new().format_finite(v).as_bytes());
        } else {
            self.buf.extend_from_slice(b"null");
        }
        Ok(())
    }
    fn serialize_f64(self, v: f64) -> Result<(), Error> {
        if v.is_finite() {
            self.buf
                .extend_from_slice(ryu::Buffer::new().format_finite(v).as_bytes());
        } else {
            self.buf.extend_from_slice(b"null");
        }
        Ok(())
    }
    fn serialize_char(self, v: char) -> Result<(), Error> {
        self.write_str(v.encode_utf8(&mut [0; 4]));
        Ok(())
    }
    fn serialize_str(self, v: &str) -> Result<(), Error> {
        self.write_str(v);
        Ok(())
    }
    fn serialize_bytes(self, v: &[u8]) -> Result<(), Error> {
        ser::Serializer::collect_seq(self, v)
    }
    fn serialize_none(self) -> Result<(), Error> {
        self.buf.extend_from_slice(b"null");
        Ok(())
    }
    fn serialize_some<T: ?Sized + Serialize>(self, value: &T) -> Result<(), Error> {
        value.serialize(self)
    }
    fn serialize_unit(self) -> Result<(), Error> {
        self.buf.extend_from_slice(b"null");
        Ok(())
    }
    fn serialize_unit_struct(self, _name: &'static str) -> Result<(), Error> {
        self.serialize_unit()
    }
    fn serialize_unit_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
    ) -> Result<(), Error> {
        self.write_ident(variant);
        Ok(())
    }
    fn serialize_newtype_struct<T: ?Sized + Serialize>(
        self,
        _name: &'static str,
        value: &T,
    ) -> Result<(), Error> {
        value.serialize(self)
    }
    fn serialize_newtype_variant<T: ?Sized + Serialize>(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        value: &T,
    ) -> Result<(), Error> {
        self.begin_variant(variant);
        value.serialize(&mut *self)?;
        self.buf.push(b'}');
        Ok(())
    }
    fn serialize_seq(self, _len: Option<usize>) -> Result<Compound<'a, W>, Error> {
        Ok(Compound::new(self, b"[", b"]"))
    }
    fn serialize_tuple(self, _len: usize) -> Result<Compound<'a, W>, Error> {
        Ok(Compound::new(self, b"[", b"]"))
    }
    fn serialize_tuple_struct(
        self,
        _name: &'static str,
        _len: usize,
    ) -> Result<Compound<'a, W>, Error> {
        Ok(Compound::new(self, b"[", b"]"))
    }
    fn serialize_tuple_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Compound<'a, W>, Error> {
        self.begin_variant(variant);
        Ok(Compound::new(self, b"[", b"]}"))
    }
    fn serialize_map(self, _len: Option<usize>) -> Result<Compound<'a, W>, Error> {
        Ok(Compound::new(self, b"{", b"}"))
    }
    fn serialize_struct(self, _name: &'static str, _len: usize) -> Result<Compound<'a, W>, Error> {
        Ok(Compound::new(self, b"[", b"]"))
    }
    fn serialize_struct_variant(
        self,
        _name: &'static str,
        _variant_index: u32,
        variant: &'static str,
        _len: usize,
    ) -> Result<Compound<'a, W>, Error> {
        self.begin_variant(variant);
        Ok(Compound::new(self, b"[", b"]}"))
    }
}

impl<W: Write> ser::SerializeSeq for Compound<'_, W> {
    type Ok = ();
    type Error = Error;
    fn serialize_element<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        self.element(value)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}
impl<W: Write> ser::SerializeTuple for Compound<'_, W> {
    type Ok = ();
    type Error = Error;
    fn serialize_element<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        self.element(value)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}
impl<W: Write> ser::SerializeTupleStruct for Compound<'_, W> {
    type Ok = ();
    type Error = Error;
    fn serialize_field<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        self.element(value)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}
impl<W: Write> ser::SerializeTupleVariant for Compound<'_, W> {
    type Ok = ();
    type Error = Error;
    fn serialize_field<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        self.element(value)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}
impl<W: Write> ser::SerializeStruct for Compound<'_, W> {
    type Ok = ();
    type Error = Error;
    fn serialize_field<T: ?Sized + Serialize>(
        &mut self,
        _key: &'static str,
        value: &T,
    ) -> Result<(), Error> {
        self.element(value)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}
impl<W: Write> ser::SerializeStructVariant for Compound<'_, W> {
    type Ok = ();
    type Error = Error;
    fn serialize_field<T: ?Sized + Serialize>(
        &mut self,
        _key: &'static str,
        value: &T,
    ) -> Result<(), Error> {
        self.element(value)
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}
impl<W: Write> ser::SerializeMap for Compound<'_, W> {
    type Ok = ();
    type Error = Error;
    fn serialize_key<T: ?Sized + Serialize>(&mut self, key: &T) -> Result<(), Error> {
        if !self.first {
            self.ser.buf.push(b',');
        }
        self.first = false;
        let start = self.ser.buf.len();
        key.serialize(&mut *self.ser)?;
        // JSON keys must be strings: quote the key if it wasn't a string (like `serde_json` does
        // for integer keys).
        if self.ser.buf.get(start) != Some(&b'"') {
            self.ser.buf.insert(start, b'"');
            self.ser.buf.push(b'"');
        }
        self.ser.buf.push(b':');
        Ok(())
    }
    fn serialize_value<T: ?Sized + Serialize>(&mut self, value: &T) -> Result<(), Error> {
        value.serialize(&mut *self.ser)?;
        self.ser.maybe_flush()
    }
    fn end(self) -> Result<(), Error> {
        Compound::end(self)
    }
}
