import Mathlib
import LeanQEC.Stabilizer.Basic
import LeanQEC.Unitary.Paulis.Basic

structure SubsystemCode (n : ℕ) extends StabCode n where
  gauge : Subgroup (@PauliGroup_group n)
  h_stab_le : stabs ≤ gauge
  h_stab_central : gauge ≤ Subgroup.centralizer (stabs : Set (PauliGroup_group n))
