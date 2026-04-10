import STLC

def main (args : List String) : IO Unit := do
  match args with
  -- Case: stlc <file_path>
  | [path] => runFile path

  -- Case: No arguments -> Start REPL
  | [] =>
    IO.println "Welcome to the STLC REPL. Type :q to quit."
    repl

  -- Case: Incorrect usage
  | _ =>
    IO.println "Usage:"
    IO.println "  stlc           # Start interactive REPL"
    IO.println "  stlc <file>    # Run a specific file"
