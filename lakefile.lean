import Lake
open System Lake DSL

package «ATP_Test»{
}

require quantumInfo from git "https://github.com/Timeroot/Lean-QuantumInfo" @ "main"


@[default_target]
lean_lib ATPTest
