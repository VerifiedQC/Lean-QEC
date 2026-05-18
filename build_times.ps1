lake build LeanQEC.Stabilizer.BitVecSATToDist
lake build LeanQEC.ComputerAlgebra.BitVecSAT
lake build LeanQEC.ComputerAlgebra.BitVecCorrectness
(measure-command { lake build LeanQEC.Stabilizer.Examples.Steane_bm }).TotalSeconds
(measure-command { lake build LeanQEC.Stabilizer.Examples.Golay_bm }).TotalSeconds
(measure-command { lake build LeanQEC.Stabilizer.Examples.BB.BB18_bm }).TotalSeconds
(measure-command { lake build LeanQEC.Stabilizer.Examples.BB.BB54_bm }).TotalSeconds
(measure-command { lake build LeanQEC.Stabilizer.Examples.BB.BB70_bm }).TotalSeconds
(measure-command { lake build LeanQEC.Stabilizer.Examples.BB.BB72_bm }).TotalSeconds
(measure-command { lake build LeanQEC.Stabilizer.Examples.BB.BB90_bm }).TotalSeconds
(measure-command { lake build LeanQEC.Stabilizer.Examples.BB.GB54_bm }).TotalSeconds

