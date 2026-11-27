import Lean

/-!
# Declaration-name dump for lemma suggestions

`#harness_dump_names "path"` writes the name of every non-internal
declaration in the current environment to `path`, one per line, and logs
`HARNESS_NAMES_OK <count>`.

The server runs it once per set of imports and uses the list to suggest
existing names when a proof uses an unknown identifier. Only the server
runs it: model-written proofs may not contain `#` commands.
-/

namespace Harness

open Lean Elab Command

syntax (name := harnessDumpNames) "#harness_dump_names " str : command

@[command_elab harnessDumpNames]
def elabHarnessDumpNames : CommandElab
  | `(#harness_dump_names $path:str) => do
    let env ← getEnv
    let mut out : Array String := #[]
    for (name, _) in env.constants.toList do
      unless name.isInternal do
        out := out.push name.toString
    IO.FS.writeFile path.getString (String.intercalate "\n" out.toList ++ "\n")
    logInfo m!"HARNESS_NAMES_OK {out.size}"
  | _ => throwUnsupportedSyntax

end Harness
