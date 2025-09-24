import Lake
open System Lake DSL

package «ATP_Test»{
    moreLinkArgs := #[
    "-L./.lake/packages/LeanCopilot/.lake/build/lib",
    "-lctranslate2"
  ]
}

require LeanCopilot from git "https://github.com/lean-dojo/LeanCopilot.git" @ "c7fbf6"

require quantumInfo from git "https://github.com/Timeroot/Lean-QuantumInfo"


@[default_target]
lean_lib ATPTest
