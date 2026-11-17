module

public import QuantumInfo.ForMathlib.Matrix
public import QuantumInfo.ForMathlib.HermitianMat.Unitary

@[expose] public section

noncomputable section

namespace Matrix

open scoped Kronecker

variable {ι : Type*} [Fintype ι] {d : ι → Type*} {R : Type*}

@[simp]
theorem piProd_apply [CommMonoid R] (A : ∀ i, Matrix (d i) (d i) R) (j k : ∀ i, d i) :
    piProd A j k = ∏ i, A i (j i) (k i) :=
  rfl

theorem piProd_smul [CommMonoid R] (c : ι → R) (A : ∀ i, Matrix (d i) (d i) R) :
    piProd (fun i => c i • A i) = (∏ i, c i) • piProd A := by
  ext j k
  simp [Finset.prod_mul_distrib]

theorem conjTranspose_piProd [CommSemiring R] [StarRing R] (A : ∀ i, Matrix (d i) (d i) R) :
    (piProd A)ᴴ = piProd (fun i => (A i)ᴴ) := by
  ext j k
  simp [star_prod]

theorem star_piProd [CommSemiring R] [StarRing R] (A : ∀ i, Matrix (d i) (d i) R) :
    star (piProd A) = piProd (fun i => star (A i)) :=
  conjTranspose_piProd A

@[simp]
theorem piProd_one [CommSemiring R] [∀ i, DecidableEq (d i)] :
    piProd (fun i => (1 : Matrix (d i) (d i) R)) = 1 := by
  ext j k
  simp only [piProd_apply, one_apply]
  rw [Finset.prod_ite_zero]
  simp [funext_iff]

variable [DecidableEq ι] [∀ i, Fintype (d i)]

theorem piProd_mul [CommSemiring R] (A B : ∀ i, Matrix (d i) (d i) R) :
    piProd (fun i => A i * B i) = piProd A * piProd B := by
  ext j k
  simp only [piProd_apply, mul_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

theorem piProd_mulVec_prod [CommSemiring R] (A : ∀ i, Matrix (d i) (d i) R)
    (v : ∀ i, d i → R) :
    piProd A *ᵥ (fun j => ∏ i, v i (j i)) = fun j => ∏ i, (A i *ᵥ v i) (j i) := by
  ext j
  simp only [mulVec, dotProduct, piProd_apply]
  rw [Fintype.prod_sum]
  simp [Finset.prod_mul_distrib]

variable [∀ i, DecidableEq (d i)]

theorem piProd_mem_unitaryGroup (A : ∀ i, 𝐔[d i]) :
    piProd (fun i => (A i : Matrix (d i) (d i) ℂ)) ∈ 𝐔[∀ i, d i] := by
  rw [mem_unitaryGroup_iff', star_piProd, ← piProd_mul]
  simp [(A _).2.1]

def unitaryPiProd (A : ∀ i, 𝐔[d i]) : 𝐔[∀ i, d i] :=
  ⟨_, piProd_mem_unitaryGroup A⟩

@[simp]
theorem unitaryPiProd_val (A : ∀ i, 𝐔[d i]) :
    (unitaryPiProd A : Matrix (∀ i, d i) (∀ i, d i) ℂ) = piProd (fun i => (A i : Matrix _ _ ℂ)) :=
  rfl

theorem unitaryPiProd_mul (A B : ∀ i, 𝐔[d i]) :
    unitaryPiProd (fun i => A i * B i) = unitaryPiProd A * unitaryPiProd B :=
  Subtype.ext (piProd_mul _ _)

@[simp]
theorem unitaryPiProd_one : unitaryPiProd (fun i => (1 : 𝐔[d i])) = 1 :=
  Subtype.ext piProd_one

end Matrix

namespace Matrix

open scoped Kronecker

variable {Q : Type*} {R : Type*} [CommMonoid R]

theorem piProd_append {n₁ n₂ : ℕ} (A : Fin n₁ → Matrix Q Q R) (B : Fin n₂ → Matrix Q Q R) :
    reindex (Fin.appendEquiv n₁ n₂) (Fin.appendEquiv n₁ n₂)
      (kroneckerMap (· * ·) (piProd A) (piProd B)) = piProd (Fin.append A B) := by
  ext j k
  rw [← (Fin.appendEquiv n₁ n₂).apply_symm_apply j, ← (Fin.appendEquiv n₁ n₂).apply_symm_apply k]
  generalize (Fin.appendEquiv n₁ n₂).symm j = x
  generalize (Fin.appendEquiv n₁ n₂).symm k = y
  simp only [reindex_apply, submatrix_apply, Equiv.symm_apply_apply, kroneckerMap_apply,
    piProd_apply, Fin.prod_univ_add]
  simp [Fin.appendEquiv]

end Matrix

theorem List.prod_ofFn_sum_eq_one {R : Type*} [Ring R] : ∀ {m : ℕ} (Q : Fin m → ZMod 2 → R)
    (_ : ∀ j, Q j 0 + Q j 1 = 1), ∑ s : Fin m → ZMod 2, (List.ofFn fun j => Q j (s j)).prod = 1
  | 0, Q, _ => by simp
  | m + 1, Q, h => by
    rw [← (Fin.consEquiv (fun _ : Fin (m + 1) => ZMod 2)).sum_comp, Fintype.sum_prod_type]
    simp only [Fin.consEquiv_apply, List.ofFn_succ, Fin.cons_zero, Fin.cons_succ, List.prod_cons]
    simp_rw [← Finset.mul_sum]
    rw [List.prod_ofFn_sum_eq_one (fun j => Q j.succ) (fun j => h j.succ), ← Finset.sum_mul,
      mul_one]
    exact (Fin.sum_univ_two (Q 0)).trans (h 0)

theorem List.prod_ofFn_selfAdjoint_idem {R : Type*} [Ring R] [StarRing R] :
    ∀ {m : ℕ} (P : Fin m → R) (_ : ∀ j, IsSelfAdjoint (P j)) (_ : ∀ j, IsIdempotentElem (P j))
    (_ : ∀ i j, Commute (P i) (P j)),
    IsSelfAdjoint (List.ofFn P).prod ∧ IsIdempotentElem (List.ofFn P).prod
  | 0, P, _, _, _ => by simp [IsIdempotentElem]
  | m + 1, P, hsa, hid, hc => by
    obtain ⟨ih1, ih2⟩ := List.prod_ofFn_selfAdjoint_idem (fun j => P j.succ) (fun j => hsa _)
      (fun j => hid _) (fun i j => hc _ _)
    have hcomm : Commute (P 0) (List.ofFn fun j : Fin m => P j.succ).prod := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp hx
      exact hc 0 j.succ
    rw [List.ofFn_succ, List.prod_cons]
    exact ⟨by rw [IsSelfAdjoint, star_mul, ih1.star_eq, (hsa 0).star_eq, hcomm.eq],
      (hid 0).mul_of_commute hcomm ih2⟩
