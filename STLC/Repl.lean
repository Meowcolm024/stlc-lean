import STLC.Parser
import STLC.Syntax
import STLC.TypeCheck
import STLC.Norm
import STLC.NbE

open Syntax

def process (raw : Raw) : IO Unit :=
  match TypeCheck.infer [] raw with
  | .error msg    => IO.println s!"\x1b[31m[Type Error]\x1b[0m {msg}"
  | .ok (.mk _ M) => do
    IO.println (List.replicate 40 '-').asString

    -- Weak reduction section
    IO.println s!"\x1b[1;32mWeak Reduction:\x1b[0m"
    let .mk N trace _ := Norm.halts M
    IO.println s!"  {M} —→* {N}"
    IO.println s!"\x1b[1;32mReduction Trace:\x1b[0m\n{trace}"

    IO.println (List.replicate 40 '-').asString

    -- Normalization section
    IO.println s!"\x1b[1;34mStrong Normalization (NbE):\x1b[0m"
    IO.println s!"  {M} ⇓ {NbE.norm M}"
    IO.println (List.replicate 40 '-').asString

partial def repl : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  let rec loop : IO Unit := do
    stdout.putStr s!"> "
    stdout.flush

    let input ← stdin.getLine
    let line := input.trim

    -- Handle Quit
    if line == ":q" then
      IO.println "Goodbye!"
      return ()

    -- Handle Empty Input
    else if line.isEmpty then
      loop

    -- Parse, Type Check and Evaluate
    else
      match Parser.parseRaw.run line with
      | .error msg => IO.println s!"\x1b[31m[Parse Error]\x1b[0m {msg}"
      | .ok raw    => process raw
      loop

  loop

def runFile (path : String) : IO Unit := do
  if ← System.FilePath.pathExists path then
    let contents ← IO.FS.readFile path
    let line := contents.trim
    if line.isEmpty then
      IO.println s!"Error: File '{path}' is empty."
    else
      IO.println s!"> {line}"
      match Parser.parseRaw.run line with
      | .error msg => IO.println s!"Parse Error in {path}: {msg}"
      | .ok raw    => process raw
  else
    IO.println s!"Error: File '{path}' not found."
