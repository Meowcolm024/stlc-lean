import STLC

def main (args : List String) : IO Unit := do
  match args with
  -- Case: leanc-program <file_path> <gas>
  | [path, gasStr] =>
    match gasStr.toNat? with
    | some g => runFile path g
    | none   => IO.println "Error: Gas must be a number."

  -- Case: No arguments -> Start REPL
  | [] =>
    IO.println "Welcome to the Lambda REPL. Type :q to quit."
    repl

  -- Case: Incorrect usage
  | _ =>
    IO.println "Usage:"
    IO.println "  <executable>                # Start interactive REPL"
    IO.println "  <executable> <file> <gas>   # Run a specific file"
