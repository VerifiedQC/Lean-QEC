import Lake
open System Lake DSL

package «LeanQEC» where
  lintDriver := "batteries/runLinter"

require physlib from git
  "https://github.com/leanprover-community/physlib.git" @ "d0ee4af6f490ce3811842fe874463bea8a33f4be"

@[default_target]
lean_lib LeanQEC
