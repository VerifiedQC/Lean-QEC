import Lake
open System Lake DSL

package «ATP_Test»{
}

require smt from git "https://github.com/ufmg-smite/lean-smt" @ "main"


@[default_target]
lean_lib ATPTest
