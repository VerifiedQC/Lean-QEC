import Mathlib
import LeanQEC.Stabilizer.Subsystem.RLG
import LeanQEC.Stabilizer.Subsystem.GridLines

/-!
# Distance of the RLG subsystem code

The dressed distance of the RLG code on an `l`-dimensional lattice is exactly `2^l`.

* Upper bound: the `X` operator supported on the `2^l` corners of a non-degenerate cube commutes
  with every box stabilizer but is not a product of gauge lines.
* Lower bound: `Grid.two_pow_le_hammingNorm`, transported from the grid to the flat qubit
  indexing `Fin r.n`.
-/

open Finset

set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

namespace RLG
variable {l : ℕ} (r : RLG l)

/-! ### Gauge lines as a linear span -/

/-- Span of the gauge line supports, in flat qubit coordinates. -/
def lineSpan' : Submodule (ZMod 2) (Fin r.n → ZMod 2) :=
  Submodule.span (ZMod 2) (Set.range fun p : Fin l × r.Coord => r.lineVec p.1 p.2)

lemma lineVec_mem_lineSpan' (i : Fin l) (c : r.Coord) : r.lineVec i c ∈ r.lineSpan' :=
  Submodule.subset_span ⟨(i, c), rfl⟩

lemma xPauli_mem_gauge_of_mem {v : Fin r.n → ZMod 2} (hv : v ∈ r.lineSpan') :
    xPauli v ∈ r.gauge := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨i, c⟩, rfl⟩ := hv
    exact Subgroup.subset_closure (Or.inl ⟨(i, c), rfl⟩)
  | zero => rw [xPauli_zero]; exact one_mem _
  | add v w _ _ hv hw => rw [← xPauli_mul]; exact mul_mem hv hw
  | smul a v _ hv =>
    rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a with rfl | rfl
    · rw [zero_smul, xPauli_zero]; exact one_mem _
    · rw [one_smul]; exact hv

lemma zPauli_mem_gauge_of_mem {v : Fin r.n → ZMod 2} (hv : v ∈ r.lineSpan') :
    zPauli v ∈ r.gauge := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨i, c⟩, rfl⟩ := hv
    exact Subgroup.subset_closure (Or.inr ⟨(i, c), rfl⟩)
  | zero => rw [zPauli_zero]; exact one_mem _
  | add v w _ _ hv hw => rw [← zPauli_mul]; exact mul_mem hv hw
  | smul a v _ hv =>
    rcases (show ∀ a : ZMod 2, a = 0 ∨ a = 1 by decide) a with rfl | rfl
    · rw [zero_smul, zPauli_zero]; exact one_mem _
    · rw [one_smul]; exact hv

lemma Pauli_toBinSympPauli_inv {n : ℕ} (g : PauliGroup_group n) :
    Pauli_toBinSympPauli g⁻¹ = - Pauli_toBinSympPauli g := by
  have h := map_inv (PauliGroup.phi n) g
  simp only [PauliGroup.phi_apply] at h
  have := congrArg Multiplicative.toAdd h
  simpa using this

/-- Both halves of the binary symplectic vector of a gauge element lie in the line span. -/
lemma gauge_toBinSymp {g : PauliGroup_group r.n} (hg : g ∈ r.gauge) :
    (Pauli_toBinSympPauli g).1 ∈ r.lineSpan' ∧ (Pauli_toBinSympPauli g).2 ∈ r.lineSpan' := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
    rcases hg with ⟨⟨i, c⟩, rfl⟩ | ⟨⟨i, c⟩, rfl⟩
    · simp only [toBinSymp_xPauli]
      exact ⟨r.lineVec_mem_lineSpan' i c, zero_mem _⟩
    · simp only [toBinSymp_zPauli]
      exact ⟨zero_mem _, r.lineVec_mem_lineSpan' i c⟩
  | one => simp only [Pauli_toBinSympPauli_one]; exact ⟨zero_mem _, zero_mem _⟩
  | mul g h _ _ hg hh =>
    rw [Pauli_to_BinSymp_correct]
    exact ⟨add_mem hg.1 hh.1, add_mem hg.2 hh.2⟩
  | inv g _ hg =>
    rw [Pauli_toBinSympPauli_inv]
    exact ⟨neg_mem hg.1, neg_mem hg.2⟩

/-- Membership in the gauge group up to phase, in binary symplectic terms. -/
lemma mem_trivialDressed_iff (E : PauliGroup_group r.n) :
    E ∈ r.toSubsystemCode.trivialDressed ↔
      (Pauli_toBinSympPauli E).1 ∈ r.lineSpan' ∧ (Pauli_toBinSympPauli E).2 ∈ r.lineSpan' := by
  rw [SubsystemCode.mem_trivialDressed_iff]
  constructor
  · rintro ⟨g, hg, hEq⟩
    rw [← hEq]
    exact r.gauge_toBinSymp hg
  · rintro ⟨hx, hz⟩
    refine ⟨xPauli (Pauli_toBinSympPauli E).1 * zPauli (Pauli_toBinSympPauli E).2,
      mul_mem (r.xPauli_mem_gauge_of_mem hx) (r.zPauli_mem_gauge_of_mem hz), ?_⟩
    rw [Pauli_to_BinSymp_correct, toBinSymp_xPauli, toBinSymp_zPauli]
    ext <;> simp

/-! ### The normalizer in terms of boxes -/

lemma stabMat'_stabIdxEquiv (i : Fin l) (a b : r.Coord) :
    r.stabMat' (r.stabIdxEquiv (i, a, b)) = r.boxVec i a b := by
  rw [stabMat'_apply, Equiv.symm_apply_apply]

/-- `E` commutes with all stabilizers iff both halves of its symplectic vector have even
overlap with every box. -/
lemma mem_normalizerGroup_iff (E : PauliGroup_group r.n) :
    E ∈ r.stabCode.normalizerGroup ↔
      ∀ i a b, r.boxVec i a b ⬝ᵥ (Pauli_toBinSympPauli E).1 = 0 ∧
        r.boxVec i a b ⬝ᵥ (Pauli_toBinSympPauli E).2 = 0 := by
  rw [r.stabCode.mem_normalizerGroup_of_closure rfl]
  simp only [BinSympMatrix.toStabSet, Finset.coe_image, Set.mem_image, Finset.mem_coe,
    Finset.mem_univ, true_and, forall_exists_index, forall_apply_eq_imp_iff]
  have hcomm : ∀ bp : BinSympPauli r.n, commute E (BinSympPauli_toPauli bp) ↔
      symplecticProd (Pauli_toBinSympPauli E) bp = 0 := fun bp => by
    rw [commute_iff_symplecticProd_zero, Pauli_toBinSympPauli_BinSympPauli_toPauli]
  simp only [hcomm]
  constructor
  · intro h i a b
    have h₁ := h (Fin.castAdd _ (r.stabIdxEquiv (i, a, b)))
    have h₂ := h (Fin.natAdd _ (r.stabIdxEquiv (i, a, b)))
    rw [cssRow_castAdd, stabMat'_stabIdxEquiv] at h₁
    rw [cssRow_natAdd, stabMat'_stabIdxEquiv] at h₂
    simp only [symplecticProd, dotProduct_zero, zero_dotProduct, add_zero, zero_add] at h₁ h₂
    exact ⟨by rw [dotProduct_comm]; exact h₁, by rw [dotProduct_comm]; exact h₂⟩
  · intro h idx
    refine Fin.addCases (fun j => ?_) (fun j => ?_) idx
    · rw [cssRow_castAdd, stabMat'_apply]
      simp only [symplecticProd, dotProduct_zero, zero_dotProduct, add_zero, zero_add]
      rw [dotProduct_comm]; exact (h _ _ _).1
    · rw [cssRow_natAdd, stabMat'_apply]
      simp only [symplecticProd, dotProduct_zero, zero_dotProduct, add_zero, zero_add]
      rw [dotProduct_comm]; exact (h _ _ _).2

/-! ### Weights -/

lemma hammingNorm_axisBox (S : r.AxisSet) :
    hammingNorm (r.axisBox S) = (Fintype.piFinset S).card := by
  unfold hammingNorm axisBox
  rw [← Finset.card_map r.coordEquiv.toEmbedding]
  congr 1
  ext k
  simp [Finset.mem_map_equiv]

lemma hammingNorm_le_union_weight (x z : Fin r.n → ZMod 2) :
    hammingNorm x ≤ union_weight x z := by
  unfold hammingNorm union_weight
  refine Finset.card_le_card fun i => ?_
  simp only [mem_filter, mem_univ, true_and, ne_eq]
  intro hx h
  exact hx ((ZMod2_or_eq_zero_iff _ _).1 h).1

lemma hammingNorm_le_union_weight' (x z : Fin r.n → ZMod 2) :
    hammingNorm z ≤ union_weight x z := by
  unfold hammingNorm union_weight
  refine Finset.card_le_card fun i => ?_
  simp only [mem_filter, mem_univ, true_and, ne_eq]
  intro hz h
  exact hz ((ZMod2_or_eq_zero_iff _ _).1 h).2

/-! ### The cube: upper bound -/

/-- Indicator of the `2^l` corners of the cube spanned by `a` and `b`. -/
def cubeVec (a b : r.Coord) : Fin r.n → ZMod 2 := r.axisBox fun j => {a j, b j}

lemma cubeVec_dot_boxVec {a b : r.Coord} (hab : ∀ j, a j ≠ b j) (i : Fin l) (a' b' : r.Coord) :
    r.cubeVec a b ⬝ᵥ r.boxVec i a' b' = 0 := by
  unfold boxVec
  split_ifs
  · apply r.axisBox_dot_eq_zero _ _ i
    rw [boxSet_self, inter_univ, card_pair (hab i)]
    exact even_two
  · simp

lemma lineVec_dot_cubeVec {a b : r.Coord} (hab : ∀ j, a j ≠ b j) (i : Fin l) (c : r.Coord) :
    r.lineVec i c ⬝ᵥ r.cubeVec a b = 0 := by
  apply r.axisBox_dot_eq_zero _ _ i
  rw [lineSet_self, univ_inter, card_pair (hab i)]
  exact even_two

lemma dot_cubeVec_eq_zero_of_mem {a b : r.Coord} (hab : ∀ j, a j ≠ b j)
    {v : Fin r.n → ZMod 2} (hv : v ∈ r.lineSpan') : v ⬝ᵥ r.cubeVec a b = 0 := by
  induction hv using Submodule.span_induction with
  | mem v hv =>
    obtain ⟨⟨i, c⟩, rfl⟩ := hv
    exact r.lineVec_dot_cubeVec hab i c
  | zero => simp
  | add v w _ _ hv hw => rw [add_dotProduct, hv, hw, add_zero]
  | smul c v _ hv => rw [smul_dotProduct, hv, smul_zero]

/-- Two cubes sharing only the corner `a` meet in exactly one qubit. -/
lemma cubeVec_dot_cubeVec (a b b' : r.Coord) (h : ∀ j, b' j ≠ a j ∧ b' j ≠ b j) :
    r.cubeVec a b ⬝ᵥ r.cubeVec a b' = 1 := by
  unfold cubeVec
  rw [axisBox_dot]
  have : ∀ j, ({a j, b j} ∩ {a j, b' j} : Finset (Fin (r.q j))) = {a j} := by
    intro j
    ext x
    simp only [mem_inter, mem_insert, mem_singleton]
    constructor
    · rintro ⟨h1 | h1, h2 | h2⟩
      · exact h2
      · exact absurd (h2.symm.trans h1) (h j).1
      · exact h2
      · exact absurd (h2.symm.trans h1) (h j).2
    · rintro rfl; simp
  simp [this]

/-- A point differing from both `a` and `b` in every coordinate. -/
lemma exists_third (a b : r.Coord) : ∃ b' : r.Coord, ∀ j, b' j ≠ a j ∧ b' j ≠ b j := by
  have : ∀ j, ∃ x : Fin (r.q j), x ≠ a j ∧ x ≠ b j := by
    intro j
    have hlt : ({a j, b j} : Finset (Fin (r.q j))).card < (univ : Finset (Fin (r.q j))).card := by
      rw [card_univ, Fintype.card_fin]
      have := r.h_ge4 j
      have := card_le_two (a := a j) (b := b j)
      omega
    obtain ⟨x, -, hx⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
    simp only [mem_insert, mem_singleton, not_or] at hx
    exact ⟨x, hx⟩
  choose b' hb' using this
  exact ⟨b', hb'⟩

lemma cubeVec_notMem (a b : r.Coord) : r.cubeVec a b ∉ r.lineSpan' := by
  intro hmem
  obtain ⟨b', hb'⟩ := r.exists_third a b
  have h0 := r.dot_cubeVec_eq_zero_of_mem (fun j => (hb' j).1.symm) hmem
  rw [r.cubeVec_dot_cubeVec a b b' hb'] at h0
  exact one_ne_zero h0

lemma hammingNorm_cubeVec {a b : r.Coord} (hab : ∀ j, a j ≠ b j) :
    hammingNorm (r.cubeVec a b) = 2 ^ l := by
  unfold cubeVec
  rw [hammingNorm_axisBox, Fintype.card_piFinset]
  simp [card_pair (hab _)]

/-- A non-degenerate cube exists on every RLG lattice. -/
lemma exists_cube : ∃ a b : r.Coord, ∀ j, a j ≠ b j := by
  refine ⟨fun j => ⟨0, by have := r.h_ge4 j; omega⟩, fun j => ⟨1, by have := r.h_ge4 j; omega⟩,
    fun j => ?_⟩
  simp [Fin.ext_iff]

/-- The cube `X` operator is a dressed logical of weight `2^l`. -/
theorem cube_undetectable {a b : r.Coord} (hab : ∀ j, a j ≠ b j) :
    r.toSubsystemCode.undetectable (xPauli (r.cubeVec a b)) := by
  refine ⟨?_, ?_, BinSympPauli_toPauli_normalized _⟩
  · change xPauli (r.cubeVec a b) ∈ r.stabCode.normalizerGroup
    rw [mem_normalizerGroup_iff]
    intro i a' b'
    simp only [toBinSymp_xPauli, dotProduct_zero, and_true]
    rw [dotProduct_comm]
    exact r.cubeVec_dot_boxVec hab i a' b'
  · rw [mem_trivialDressed_iff, toBinSymp_xPauli]
    exact fun h => r.cubeVec_notMem a b h.1

theorem pauli_weight_cube {a b : r.Coord} (hab : ∀ j, a j ≠ b j) :
    pauli_weight (xPauli (r.cubeVec a b)) = 2 ^ l := by
  rw [xPauli, pauli_weight_BinSympPauli_toPauli, BinSympPauli.weight, union_weight_zero_right,
    r.hammingNorm_cubeVec hab]

/-! ### Transport to the grid: lower bound -/

/-- Reindexing flat vectors by lattice coordinates. -/
def toGrid : (Fin r.n → ZMod 2) →ₗ[ZMod 2] Grid.Vec (fun i => Fin (r.q i)) :=
  LinearMap.funLeft (ZMod 2) (ZMod 2) r.coordEquiv

@[simp] lemma toGrid_apply (v : Fin r.n → ZMod 2) (c : r.Coord) :
    r.toGrid v c = v (r.coordEquiv c) := rfl

lemma toGrid_injective : Function.Injective r.toGrid :=
  LinearMap.funLeft_injective_of_surjective _ _ _ r.coordEquiv.surjective

lemma hammingNorm_toGrid (v : Fin r.n → ZMod 2) : hammingNorm (r.toGrid v) = hammingNorm v := by
  unfold hammingNorm
  rw [← Finset.card_map r.coordEquiv.toEmbedding]
  congr 1
  ext k
  simp [Finset.mem_map_equiv]

lemma axisBox_dot_eq (S : r.AxisSet) (v : Fin r.n → ZMod 2) :
    r.axisBox S ⬝ᵥ v = ∑ c, if c ∈ Fintype.piFinset S then v (r.coordEquiv c) else 0 := by
  unfold axisBox dotProduct
  rw [← r.coordEquiv.sum_comp]
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [Equiv.symm_apply_apply]
  split_ifs <;> simp

lemma toGrid_line (i : Fin l) (c : r.Coord) : r.toGrid (r.lineVec i c) = Grid.line i c := by
  funext x
  simp only [toGrid_apply, lineVec, axisBox, Equiv.symm_apply_apply, Grid.line]
  by_cases hx : x ∈ Fintype.piFinset (r.lineSet i c)
  · rw [if_pos hx, if_pos (r.mem_line_iff.1 hx)]
  · rw [if_neg hx, if_neg fun h => hx (r.mem_line_iff.2 h)]

lemma toGrid_boxSum (v : Fin r.n → ZMod 2) (i : Fin l) (a b : r.Coord) :
    Grid.boxSum (r.toGrid v) i a b = r.axisBox (r.boxSet i a b) ⬝ᵥ v := by
  rw [axisBox_dot_eq]
  unfold Grid.boxSum
  refine Finset.sum_congr rfl fun c _ => ?_
  simp only [toGrid_apply]
  by_cases hc : c ∈ Fintype.piFinset (r.boxSet i a b)
  · rw [if_pos hc, if_pos (r.mem_box_iff.1 hc)]
  · rw [if_neg hc, if_neg fun h => hc (r.mem_box_iff.2 h)]

lemma Cent_toGrid {v : Fin r.n → ZMod 2} (hv : ∀ i a b, r.boxVec i a b ⬝ᵥ v = 0) :
    Grid.Cent (r.toGrid v) := by
  intro i a b hab
  rw [toGrid_boxSum]
  have := hv i a b
  rw [boxVec, if_pos (show r.Nondeg i a b from hab)] at this
  exact this

lemma toGrid_lineSpan : Grid.lineSpan (fun i => Fin (r.q i)) = r.lineSpan'.map r.toGrid := by
  rw [lineSpan', Submodule.map_span, Grid.lineSpan, ← Set.range_comp]
  congr 2
  funext p
  exact (r.toGrid_line p.1 p.2).symm

lemma toGrid_notMem {v : Fin r.n → ZMod 2} (hv : v ∉ r.lineSpan') :
    r.toGrid v ∉ Grid.lineSpan (fun i => Fin (r.q i)) := by
  rw [toGrid_lineSpan]
  rintro ⟨w, hw, hwv⟩
  exact hv (r.toGrid_injective hwv ▸ hw)

/-- Any binary vector commuting with all boxes and outside the gauge span has weight `≥ 2^l`. -/
theorem two_pow_le_hammingNorm {v : Fin r.n → ZMod 2} (hcent : ∀ i a b, r.boxVec i a b ⬝ᵥ v = 0)
    (hv : v ∉ r.lineSpan') : 2 ^ l ≤ hammingNorm v := by
  rw [← r.hammingNorm_toGrid]
  refine Grid.two_pow_le_hammingNorm l (fun i => Fin (r.q i)) (fun i => ?_) _
    (r.Cent_toGrid hcent) (r.toGrid_notMem hv)
  rw [Fintype.card_fin]
  exact ⟨r.h_even i, r.h_ge4 i⟩

/-- Every dressed logical error has weight at least `2^l`. -/
theorem two_pow_le_pauli_weight (E : PauliGroup_group r.n)
    (hE : r.toSubsystemCode.undetectable E) : 2 ^ l ≤ pauli_weight E := by
  obtain ⟨hN, hT, -⟩ := hE
  rw [pauli_weight_eq_BinSympPauli_weight, BinSympPauli.weight]
  change E ∈ r.stabCode.normalizerGroup at hN
  rw [mem_normalizerGroup_iff] at hN
  rw [mem_trivialDressed_iff, not_and_or] at hT
  rcases hT with hT | hT
  · exact le_trans (r.two_pow_le_hammingNorm (fun i a b => (hN i a b).1) hT)
      (r.hammingNorm_le_union_weight _ _)
  · exact le_trans (r.two_pow_le_hammingNorm (fun i a b => (hN i a b).2) hT)
      (r.hammingNorm_le_union_weight' _ _)

/-! ### Main theorem -/

/-- The dressed distance of the RLG subsystem code is exactly `2^l`. -/
theorem distance_eq : r.toSubsystemCode.distance = 2 ^ l := by
  obtain ⟨a, b, hab⟩ := r.exists_cube
  exact SubsystemCode.distance_eq_of _ (r.cube_undetectable hab) (r.pauli_weight_cube hab)
    (fun F hF => r.two_pow_le_pauli_weight F hF)

/-! ### Bare distance -/

/-- `E` commutes with every gauge line iff both halves of its symplectic vector have even
overlap with every line. -/
lemma mem_bareNormalizer_iff (E : PauliGroup_group r.n) :
    E ∈ r.toSubsystemCode.bareNormalizer ↔
      ∀ i c, r.lineVec i c ⬝ᵥ (Pauli_toBinSympPauli E).1 = 0 ∧
        r.lineVec i c ⬝ᵥ (Pauli_toBinSympPauli E).2 = 0 := by
  change E ∈ Subgroup.centralizer ((Subgroup.closure r.gaugeGens : Subgroup _) : Set _) ↔ _
  rw [Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  have hcomm : ∀ bp : BinSympPauli r.n,
      BinSympPauli_toPauli bp * E = E * BinSympPauli_toPauli bp ↔
        symplecticProd (Pauli_toBinSympPauli E) bp = 0 := fun bp => by
    rw [← commute_iff_commute, commute_symm, commute_iff_symplecticProd_zero,
      Pauli_toBinSympPauli_BinSympPauli_toPauli]
  constructor
  · intro h i c
    have h₁ := h _ (Or.inl ⟨(i, c), rfl⟩)
    have h₂ := h _ (Or.inr ⟨(i, c), rfl⟩)
    dsimp only at h₁ h₂
    rw [xPauli, hcomm] at h₁
    rw [zPauli, hcomm] at h₂
    simp only [symplecticProd, dotProduct_zero, zero_dotProduct, add_zero, zero_add] at h₁ h₂
    exact ⟨by rw [dotProduct_comm]; exact h₂, by rw [dotProduct_comm]; exact h₁⟩
  · rintro h g (⟨⟨i, c⟩, rfl⟩ | ⟨⟨i, c⟩, rfl⟩) <;> dsimp only
    · rw [xPauli, hcomm]
      simp only [symplecticProd, dotProduct_zero, zero_dotProduct, add_zero, zero_add]
      rw [dotProduct_comm]; exact (h i c).2
    · rw [zPauli, hcomm]
      simp only [symplecticProd, dotProduct_zero, zero_dotProduct, add_zero, zero_add]
      rw [dotProduct_comm]; exact (h i c).1

/-- The cube `X` operator is even a bare logical: it meets every gauge line in `0` or `2`
qubits. -/
theorem cube_bareUndetectable {a b : r.Coord} (hab : ∀ j, a j ≠ b j) :
    r.toSubsystemCode.bareUndetectable (xPauli (r.cubeVec a b)) := by
  refine ⟨?_, ?_, BinSympPauli_toPauli_normalized _⟩
  · rw [mem_bareNormalizer_iff]
    intro i c
    simp only [toBinSymp_xPauli, dotProduct_zero, and_true]
    exact r.lineVec_dot_cubeVec hab i c
  · rw [mem_trivialDressed_iff, toBinSymp_xPauli]
    exact fun h => r.cubeVec_notMem a b h.1

/-- The bare distance of the RLG subsystem code is also exactly `2^l`. -/
theorem bareDistance_eq : r.toSubsystemCode.bareDistance = 2 ^ l := by
  obtain ⟨a, b, hab⟩ := r.exists_cube
  exact SubsystemCode.bareDistance_eq_of _ (r.cube_bareUndetectable hab)
    (r.pauli_weight_cube hab) fun F hF => r.two_pow_le_pauli_weight F hF.undetectable

end RLG
