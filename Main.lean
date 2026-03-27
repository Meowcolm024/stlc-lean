import STLC

def main (args : List String) : IO Unit := do
  match args with
  -- Case: stlc <file_path> <gas>
  | [path, gasStr] =>
    match gasStr.toNat? with
    | some g => runFile path g
    | none   => IO.println "Error: Gas must be a number."

  -- Case: No arguments -> Start REPL
  | [] =>
    IO.println "Welcome to the STLC REPL. Type :q to quit."
    repl

  -- Case: Incorrect usage
  | _ =>
    IO.println "Usage:"
    IO.println "  stlc                # Start interactive REPL"
    IO.println "  stlc <file> <gas>   # Run a specific file"
