import Mathlib
import LeanQEC.Stabilizer.Basic
import LeanQEC.Unitary.Paulis.Basic

structure SubsystemCode (n : ℕ) extends StabCode n where
  gauge : Subgroup (@PauliGroup_group n)
  h_stab_le : stabs ≤ gauge
  h_stab_central : gauge ≤ Subgroup.centralizer (stabs : Set (PauliGroup_group n))

/-!
## Dressed distance of a subsystem code

An error is undetectable when it commutes with every stabilizer but is not an element of the
gauge group (up to phase): it acts nontrivially on the logical qubits. The dressed distance is
the minimum weight of such an error, with the convention `n + 1` when none exists.
-/

namespace SubsystemCode

variable {n : ℕ} (C : SubsystemCode n)

/-- Operators acting trivially on the logical qubits: gauge operators up to phase. -/
noncomputable def trivialDressed : Subgroup (PauliGroup_group n) :=
  C.gauge ⊔ PauliGroup.phaseSubgroup n

lemma trivialDressed_eq_comap :
    C.trivialDressed
      = Subgroup.comap (PauliGroup.phi n) (C.gauge.map (PauliGroup.phi n)) :=
  (Subgroup.comap_map_eq _ _).symm

lemma mem_trivialDressed_iff (E : PauliGroup_group n) :
    E ∈ C.trivialDressed ↔ ∃ g ∈ C.gauge, Pauli_toBinSympPauli g = Pauli_toBinSympPauli E := by
  rw [trivialDressed_eq_comap, Subgroup.mem_comap, Subgroup.mem_map]
  refine ⟨fun ⟨s, hs, hEq⟩ => ⟨s, hs, ?_⟩, fun ⟨s, hs, hEq⟩ => ⟨s, hs, ?_⟩⟩
  · simpa using congrArg Multiplicative.toAdd hEq
  · simpa using congrArg Multiplicative.ofAdd hEq

/-- A dressed logical error: commutes with the stabilizers, is not a gauge operator up to
phase, and carries the phase convention `+1`. -/
def undetectable (E : PauliGroup n) : Prop :=
  E ∈ C.normalizerGroup ∧ E ∉ C.trivialDressed ∧ PauliGroup.normalized E

noncomputable instance : DecidablePred fun E => C.undetectable E := Classical.decPred _

noncomputable def undetectable_set : Finset (PauliGroup n) := {E | C.undetectable E}

/-- The dressed distance: minimum weight of a dressed logical error. -/
noncomputable def distance : ℕ :=
  match Finset.min (C.undetectable_set.image pauli_weight) with
  | ⊤ => n + 1
  | some d => d

/-- The distance is pinned down by a witness of weight `d` together with a lower bound `d` on
the weight of every dressed logical error. -/
theorem distance_eq_of {d : ℕ} {E : PauliGroup n} (hE : C.undetectable E)
    (hwE : pauli_weight E = d) (hlow : ∀ F, C.undetectable F → d ≤ pauli_weight F) :
    C.distance = d := by
  have hmem : d ∈ C.undetectable_set.image pauli_weight := by
    rw [Finset.mem_image]
    exact ⟨E, by simp [undetectable_set, hE], hwE⟩
  obtain ⟨m, hm⟩ := Finset.min_of_mem hmem
  have hle : m ≤ d := WithTop.coe_le_coe.1 (hm ▸ Finset.min_le hmem)
  have hge : d ≤ m := by
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_min hm)
    exact hlow F (by simpa [undetectable_set] using hF)
  unfold distance
  rw [hm]
  exact le_antisymm hle hge

/-!
## Bare distance

A bare logical error commutes with every gauge operator (not merely every stabilizer) and is
not a gauge operator up to phase. Every bare logical is a dressed logical, so the bare distance
is at least the dressed distance.
-/

/-- Paulis commuting with every gauge operator. -/
def bareNormalizer : Subgroup (PauliGroup_group n) :=
  Subgroup.centralizer (C.gauge : Set (PauliGroup_group n))

lemma bareNormalizer_le_normalizerGroup : C.bareNormalizer ≤ C.normalizerGroup :=
  Subgroup.centralizer_le (SetLike.coe_subset_coe.2 C.h_stab_le)

/-- A bare logical error. -/
def bareUndetectable (E : PauliGroup n) : Prop :=
  E ∈ C.bareNormalizer ∧ E ∉ C.trivialDressed ∧ PauliGroup.normalized E

lemma bareUndetectable.undetectable {E : PauliGroup n} (h : C.bareUndetectable E) :
    C.undetectable E :=
  ⟨C.bareNormalizer_le_normalizerGroup h.1, h.2.1, h.2.2⟩

noncomputable instance : DecidablePred fun E => C.bareUndetectable E := Classical.decPred _

noncomputable def bareUndetectable_set : Finset (PauliGroup n) := {E | C.bareUndetectable E}

lemma bareUndetectable_set_subset : C.bareUndetectable_set ⊆ C.undetectable_set := by
  intro E hE
  simp only [bareUndetectable_set, undetectable_set, Finset.mem_filter, Finset.mem_univ,
    true_and] at hE ⊢
  exact hE.undetectable

/-- The bare distance: minimum weight of a bare logical error, `n + 1` if there is none. -/
noncomputable def bareDistance : ℕ :=
  match Finset.min (C.bareUndetectable_set.image pauli_weight) with
  | ⊤ => n + 1
  | some d => d

theorem bareDistance_eq_of {d : ℕ} {E : PauliGroup n} (hE : C.bareUndetectable E)
    (hwE : pauli_weight E = d) (hlow : ∀ F, C.bareUndetectable F → d ≤ pauli_weight F) :
    C.bareDistance = d := by
  have hmem : d ∈ C.bareUndetectable_set.image pauli_weight := by
    rw [Finset.mem_image]
    exact ⟨E, by simp [bareUndetectable_set, hE], hwE⟩
  obtain ⟨m, hm⟩ := Finset.min_of_mem hmem
  have hle : m ≤ d := WithTop.coe_le_coe.1 (hm ▸ Finset.min_le hmem)
  have hge : d ≤ m := by
    obtain ⟨F, hF, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_min hm)
    exact hlow F (by simpa [bareUndetectable_set] using hF)
  unfold bareDistance
  rw [hm]
  exact le_antisymm hle hge

lemma pauli_weight_le (E : PauliGroup n) : pauli_weight E ≤ n := by
  unfold pauli_weight
  exact (Finset.card_filter_le _ _).trans (by simp)

/-- The dressed distance never exceeds the bare distance. -/
theorem distance_le_bareDistance : C.distance ≤ C.bareDistance := by
  have hsub := Finset.image_subset_image (f := pauli_weight) C.bareUndetectable_set_subset
  unfold distance bareDistance
  split
  · rename_i hd
    split
    · exact le_rfl
    · rename_i m hm
      exfalso
      have hm' := hsub (Finset.mem_of_min hm)
      rw [Finset.min_eq_top.1 hd] at hm'
      exact Finset.notMem_empty _ hm'
  · rename_i d hd
    split
    · obtain ⟨F, -, rfl⟩ := Finset.mem_image.1 (Finset.mem_of_min hd)
      exact Nat.le_succ_of_le (pauli_weight_le F)
    · rename_i m hm
      have hm' := Finset.min_le (hsub (Finset.mem_of_min hm))
      rw [hd] at hm'
      exact WithTop.coe_le_coe.1 hm'

end SubsystemCode
