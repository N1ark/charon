import Charon

open Charon

def usage : String := "Usage:
  charon-lean print <file.(u)llbc.postcard>
      Pretty-print a file emitted by `charon --format postcard`.
  charon-lean repr <file.(u)llbc.postcard>
      Dump the whole deserialized AST using the derived `Repr` instances.
  charon-lean check <file.(u)llbc.postcard>...
      Deserialize the given files and report the time it took.
  charon-lean (rustc|cargo) [charon options] [-- <rustc/cargo options>]
      Run charon and pretty-print the result. By default, this extracts the ULLBC that is the
      closest to MIR (`--preset=raw-mir`); all the charon options are supported.

The charon binary is taken from the `CHARON_BIN` environment variable, or `charon` otherwise."

/-- Runs charon with the given arguments and loads the resulting crate. -/
def runCharon (subcommand : String) (args : List String) : IO CrateData := do
  let charon := (← IO.getEnv "CHARON_BIN").getD "charon"
  let (charonArgs, extraArgs) := match args.idxOf? "--" with
    | some i => (args.take i, args.drop i)
    | none => (args, [])
  -- Extract the code that is the closest to MIR unless asked otherwise.
  let preset := if charonArgs.any (·.startsWith "--preset") then [] else ["--preset=raw-mir"]
  IO.FS.withTempDir fun dir => do
    let dest := dir / "crate.llbc.postcard"
    let child ← IO.Process.spawn {
      cmd := charon
      args := (([subcommand] ++ preset ++ charonArgs ++
        ["--format=postcard", "--dest-file", dest.toString] ++ extraArgs).toArray)
    }
    let code ← child.wait
    if code != 0 then
      throw <| IO.userError s!"charon exited with code {code}"
    CrateData.ofPostcardFile dest

def main (args : List String) : IO UInt32 := do
  match args with
  | ["print", file] =>
    let data ← CrateData.ofPostcardFile file
    IO.print data.translated.toPrettyString
    return 0
  | ["repr", file] =>
    let data ← CrateData.ofPostcardFile file
    IO.println (repr data.translated).pretty
    return 0
  | "check" :: files@(_ :: _) =>
    for file in files do
      let start ← IO.monoMsNow
      let data ← CrateData.ofPostcardFile file
      let time := (← IO.monoMsNow) - start
      let k := data.translated
      IO.println s!"{file}: {time}ms ({k.type_decls.values.size} types, \
        {k.fun_decls.values.size} functions, {k.global_decls.values.size} globals, \
        {k.trait_decls.values.size} traits, {k.trait_impls.values.size} impls)"
    return 0
  | subcommand :: rest =>
    if subcommand == "rustc" || subcommand == "cargo" then
      let data ← runCharon subcommand rest
      IO.print data.translated.toPrettyString
      return if data.has_errors then 1 else 0
    IO.eprintln usage
    return 1
  | [] =>
    IO.eprintln usage
    return 1
