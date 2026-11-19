import Charon.Generated.OfPostcard
import Charon.Version

/-! Reading the `.llbc`/`.ullbc` files emitted by Charon with `--format postcard`. -/

namespace Charon

/-- The contents of a file emitted by Charon; mirrors `charon_lib::export::CrateData`. -/
structure CrateData where
  /-- The version of Charon that emitted the file. -/
  charon_version : String
  translated : TranslatedCrate
  /-- If there were errors, this contains only a partial description of the input crate. -/
  has_errors : Bool
  deriving Inhabited

/-- Decodes the contents of a postcard file emitted by Charon. -/
def CrateData.ofPostcardBytes (data : ByteArray) : Except String CrateData := do
  -- Detect JSON input to give a helpful error.
  match (data.extract 0 64).toList.find? (fun b => !" \t\n\r".toList.contains (Char.ofUInt8 b)) with
  | none => throw "the input is empty"
  | some b =>
    if b == '{'.toUInt8 then
      throw "the input looks like JSON; please regenerate it with `--format postcard`"
  let decode : M CrateData := do
    let charon_version ← Postcard.string
    if charon_version != supportedCharonVersion then
      Postcard.fail s!"incompatible version of charon: this program supports llbc emitted by \
        charon v{supportedCharonVersion} but attempted to read a file emitted by charon \
        v{charon_version}"
    let translated ← TranslatedCrate.ofPostcard
    let has_errors ← Postcard.bool
    unless ← Postcard.atEnd do
      Postcard.fail "trailing bytes after the end of the crate"
    return { charon_version, translated, has_errors }
  let (crate_data, _) ← Postcard.run decode data {}
  return crate_data

def CrateData.ofPostcardFile (path : System.FilePath) : IO CrateData := do
  let data ← IO.FS.readBinFile path
  match CrateData.ofPostcardBytes data with
  | .ok crate_data => return crate_data
  | .error e => throw <| IO.userError s!"failed to deserialize {path}: {e}"

end Charon
