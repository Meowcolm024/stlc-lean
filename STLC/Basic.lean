import STLC.Parser
import STLC.Syntax
import STLC.TypeCheck
import STLC.Semantic
import STLC.NbE

open Syntax

def process (g : Nat) (raw : Raw) : IO Unit :=
  match TypeCheck.infer [] raw with
  | .error msg    => IO.println s!"\x1b[31m[Type Error]\x1b[0m {msg}"
  | .ok (.mk _ M) => do
    IO.println (List.replicate 40 '-').asString

    -- Weak reduction section
    IO.println s!"\x1b[1;32mWeak reduction (gas: {g}):\x1b[0m"
    let .mk N trace fin := Semantic.eval g M
    IO.println s!"  {M} —→* {N}"
    IO.println s!"\x1b[1;32mTrace\x1b[0m:\n{trace}"
    match fin with
    | none => IO.println "\x1b[31m[out of gas]\x1b[0m"
    | some _ => IO.println "\x1b[1;32m[finished]\x1b[0m"

    IO.println (List.replicate 40 '-').asString

    -- Normalization section
    IO.println s!"\x1b[1;34mStrong Normalization (NbE):\x1b[0m"
    IO.println s!"  {M} —→* {NbE.norm M}"
    IO.println (List.replicate 40 '-').asString

partial def repl : IO Unit := do
  let stdin ← IO.getStdin
  let stdout ← IO.getStdout

  let rec loop (gas : Nat) : IO Unit := do
    stdout.putStr s!"[{gas}] > "
    stdout.flush

    let input ← stdin.getLine
    let line := input.trim

    -- 1. Handle Quit
    if line == ":q" then
      IO.println "Goodbye!"
      return ()

    -- 2. Handle Gas Update
    if line.startsWith ":gas " then
      let valStr := line.drop 5
      match valStr.toNat? with
      | some n =>
          IO.println s!"Gas updated to {n}"
          loop n
      | none =>
          IO.println "Error: Invalid gas value."
          loop gas

    -- 3. Handle Empty Input
    else if line.isEmpty then
      loop gas

    -- 4. TODO
    else
      match Parser.parseRaw.run line with
      | .error msg => IO.println s!"Parse Error in: {msg}"
      | .ok raw    => process gas raw
      loop gas

  loop 100

def runFile (path : String) (gas : Nat) : IO Unit := do
  if ← System.FilePath.pathExists path then
    let contents ← IO.FS.readFile path
    let line := contents.trim
    if line.isEmpty then
      IO.println s!"Error: File '{path}' is empty."
    else
      IO.println s!"> {line}"
      match Parser.parseRaw.run line with
      | .error msg => IO.println s!"Parse Error in {path}: {msg}"
      | .ok raw    => process gas raw
  else
    IO.println s!"Error: File '{path}' not found."
