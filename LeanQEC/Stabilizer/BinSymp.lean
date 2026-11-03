import LeanQEC.Stabilizer.Code

variable {n : ℕ}

set_option synthInstance.maxHeartbeats 1000000

--define binary symplectic representation, yielding Finset of PauliGroup n from matrix

abbrev BinSympPauli (n : ℕ) := (Fin n → (ZMod 2)) × (Fin n → (ZMod 2))

--don't actually need these, right?
def ZMod2_or (a b : ZMod 2) := a + b + (a * b)

def union_weight (v₁ v₂ : Fin n → (ZMod 2)) : ℕ := hammingNorm (fun i => ZMod2_or (v₁ i) (v₂ i))

def BinSympPauli.weight {n : ℕ} (bsp : BinSympPauli n) : ℕ := union_weight bsp.1 bsp.2

@[simp]
lemma union_weight_zero_left (v : Fin n → ZMod 2) : union_weight 0 v = hammingNorm v := by
  unfold union_weight
  congr
  ext i
  simp [ZMod2_or]

@[simp]
lemma union_weight_zero_right (v : Fin n → ZMod 2) : union_weight v 0 = hammingNorm v := by
  unfold union_weight
  congr
  ext i
  simp [ZMod2_or]

def symplecticProd {n : ℕ} (bp₁ bp₂ : BinSympPauli n) : (ZMod 2) :=
  dotProduct bp₁.1 bp₂.2 + dotProduct bp₁.2 bp₂.1

--don't need this, we get comm group structure for free!
--def BinSympPauli_add {n : ℕ} (bp₁ bp₂ : BinSympPauli n) : BinSympPauli n := (bp₁.1 + bp₂.1, bp₁.2 + bp₂.2)

--wait, can't do this because Prod.fst isn't injective..
--lemma BinSympPauli_sum_eq (F : Finset (BinSympPauli n)) : Finset.sum F id = ((Finset.sum (F.map Prod.fst) id), (Finset.sum (F.map Prod.snd) id)) := by

noncomputable section

def Z2Z2_Pauli_equiv : ((ZMod 2) × (ZMod 2)) ≃ Pauli where
  toFun := fun
  | (0, 0) => Pauli_I
  | (1, 0) => Pauli_X
  | (0, 1) => Pauli_Z
  | (1, 1) => Pauli_Y
  invFun := fun P => --this sucks. This is what i get for not defining paulis as a type
   if h : P = Pauli_I then (0, 0) else
  if h2 : P = Pauli_X then (1, 0) else
  if h3 : P = Pauli_Z then (0, 1) else (1, 1)
  left_inv := by
    intro x
    fin_cases x <;> simp [ZMod]
  right_inv := by
    intro x
    rcases Pauli_cases x with h | h | h | h <;> simp [h]

lemma ZMod2_or_eq_zero_iff (a b : ZMod 2) :
    ZMod2_or a b = 0 ↔ a = 0 ∧ b = 0 := by
  revert a b
  native_decide

lemma Z2Z2_Pauli_equiv_ne_I_iff (a b : ZMod 2) :
    Z2Z2_Pauli_equiv (a, b) ≠ Pauli_I ↔ ZMod2_or a b ≠ 0 := by
  fin_cases a <;> fin_cases b <;> simp [ Z2Z2_Pauli_equiv, ZMod2_or ] <;> native_decide

def BinSympPauli_toPauli {n : ℕ} (bs : BinSympPauli n) : ↥(PauliGroup_group n) :=
  let pm := fun n => Z2Z2_Pauli_equiv (bs.1 n, bs.2 n)
  foldPauli (1, pm)

def Pauli_toBinSympPauli {n : ℕ} (P : ↥(PauliGroup_group n)) : BinSympPauli n :=
  let pm := fun n => Z2Z2_Pauli_equiv.symm (PauliGroup.map P n)
  ⟨fun n => (pm n).1, fun n => (pm n).2⟩

--three big linking theorems, rest is mostly extremely painful proof massaging

lemma Bool.ofNat_ZMod2_add (x y : ZMod 2) :
    Bool.xor (Bool.ofNat x.val) (Bool.ofNat y.val) = Bool.ofNat ((x + y).val) := by
  fin_cases x <;> fin_cases y <;> decide

lemma local_mul_Pauli_toBinSymp (P Q : Pauli) :
    Z2Z2_Pauli_equiv.symm (mul_Pauli1 P Q).2 =
      Z2Z2_Pauli_equiv.symm P + Z2Z2_Pauli_equiv.symm Q := by
  rcases Pauli_cases P with rfl | rfl | rfl | rfl <;>
    rcases Pauli_cases Q with rfl | rfl | rfl | rfl <;>
    simp [mul_Pauli1, Z2Z2_Pauli_equiv] <;> native_decide

lemma local_anticommute_eq_sympProd (P Q : Pauli) :
    (!commute₁ P Q) =
      Bool.ofNat
        (((Z2Z2_Pauli_equiv.symm P).1 * (Z2Z2_Pauli_equiv.symm Q).2) +
          ((Z2Z2_Pauli_equiv.symm P).2 * (Z2Z2_Pauli_equiv.symm Q).1)).val := by
  rcases Pauli_cases P with rfl | rfl | rfl | rfl <;>
    rcases Pauli_cases Q with rfl | rfl | rfl | rfl <;>
    simp [commute₁, Z2Z2_Pauli_equiv, Bool.ofNat] ; native_decide

lemma local_anticommute_xor_tail (a b c d t : ZMod 2) :
    (!commute₁ (Z2Z2_Pauli_equiv (a, b)) (Z2Z2_Pauli_equiv (c, d)) ^^ Bool.ofNat t.val) =
      Bool.ofNat (((a * d + b * c) + t).val) := by
  have hhead :
      (!commute₁ (Z2Z2_Pauli_equiv (a, b)) (Z2Z2_Pauli_equiv (c, d))) =
        Bool.ofNat ((a * d + b * c).val) := by
    simpa using
      (local_anticommute_eq_sympProd (Z2Z2_Pauli_equiv (a, b)) (Z2Z2_Pauli_equiv (c, d)))
  rw [hhead, Bool.ofNat_ZMod2_add]

@[simp]
lemma BinSympPauli_toPauli_zero {n : ℕ} : BinSympPauli_toPauli (0 : BinSympPauli n) = 1 := by
  change foldPauli (1, fun _ : Fin n => Pauli_I) = Pauli1
  simpa using Pauli1_unfold.symm

lemma BinSympPauli_toPauli_normalized {n : ℕ} (bp : BinSympPauli n) :
    PauliGroup.normalized (BinSympPauli_toPauli bp) := by
  unfold PauliGroup.normalized PauliGroup.phase BinSympPauli_toPauli
  simp [Equiv.symm_apply_apply]

@[simp]
lemma Pauli_toBinSympPauli_BinSympPauli_toPauli {n : ℕ} (bp : BinSympPauli n) :
    Pauli_toBinSympPauli (BinSympPauli_toPauli bp) = bp := by
  ext i <;> simp [Pauli_toBinSympPauli, BinSympPauli_toPauli, PauliGroup.map]

@[simp]
lemma Pauli_toBinSympPauli_normalize_pauli {n : ℕ} (P : PauliGroup n) :
    Pauli_toBinSympPauli (normalize_pauli P) = Pauli_toBinSympPauli P := by
  ext i <;> simp [Pauli_toBinSympPauli, normalize_pauli, PauliGroup.map]

@[simp]
lemma BinSympPauli_toPauli_Pauli_toBinSympPauli {n : ℕ} (P : PauliGroup n) :
    BinSympPauli_toPauli (Pauli_toBinSympPauli P) = normalize_pauli P := by
  apply Subtype.ext
  simp [BinSympPauli_toPauli, Pauli_toBinSympPauli, normalize_pauli, PauliGroup.map]

lemma PauliGroup.map_BinSympPauli_toPauli {n : ℕ} (bp : BinSympPauli n) :
    PauliGroup.map (BinSympPauli_toPauli bp) = fun i => Z2Z2_Pauli_equiv (bp.1 i, bp.2 i) := by
  funext i
  have hx := congrArg (fun bp' => bp'.1 i) (Pauli_toBinSympPauli_BinSympPauli_toPauli bp)
  have hz := congrArg (fun bp' => bp'.2 i) (Pauli_toBinSympPauli_BinSympPauli_toPauli bp)
  have hpair : Z2Z2_Pauli_equiv.symm (PauliGroup.map (BinSympPauli_toPauli bp) i) = (bp.1 i, bp.2 i) := by
    exact Prod.ext hx hz
  have := congrArg Z2Z2_Pauli_equiv hpair
  simpa using this

@[simp]
lemma Pauli_toBinSympPauli_one {n : ℕ} :
    Pauli_toBinSympPauli (1 : PauliGroup_group n) = 0 := by
  simpa [BinSympPauli_toPauli_zero] using
    (Pauli_toBinSympPauli_BinSympPauli_toPauli (0 : BinSympPauli n))

lemma pauli_weight_BinSympPauli_toPauli {n : ℕ} (bp : BinSympPauli n) :
    pauli_weight (BinSympPauli_toPauli bp) = BinSympPauli.weight bp := by
  unfold pauli_weight BinSympPauli.weight union_weight hammingNorm
  congr
  ext i
  simp [PauliGroup.map_BinSympPauli_toPauli, Z2Z2_Pauli_equiv_ne_I_iff]

lemma pauli_weight_eq_BinSympPauli_weight {n : ℕ} (P : PauliGroup n) :
    pauli_weight P = BinSympPauli.weight (Pauli_toBinSympPauli P) := by
  calc
    pauli_weight P = pauli_weight (normalize_pauli P) := by
      unfold pauli_weight
      rw [show PauliGroup.map (normalize_pauli P) = PauliGroup.map P from
        (normalize_pauli_map_eq P).symm]
    _ = BinSympPauli.weight (Pauli_toBinSympPauli P) := by
      rw [← BinSympPauli_toPauli_Pauli_toBinSympPauli P]
      exact pauli_weight_BinSympPauli_toPauli (Pauli_toBinSympPauli P)

theorem Pauli_to_BinSymp_correct {n : ℕ} (P₁ P₂ : PauliGroup_group n) :
    Pauli_toBinSympPauli (P₁ * P₂) = (Pauli_toBinSympPauli P₁) + (Pauli_toBinSympPauli P₂) := by
  let FP₁ := foldPauli.symm P₁
  let FP₂ := foldPauli.symm P₂
  have hmul : foldPauli.symm (P₁ * P₂ : PauliGroup_group n) = mul_factored_Paulis FP₁ FP₂ := by
    apply foldPauli.injective
    apply Subtype.ext
    simpa [FP₁, FP₂] using (mul_factored_Paulis_correct FP₁ FP₂).symm
  ext i
  · have hi : (foldPauli.symm (P₁ * P₂)).2 i = (mul_Pauli1 (FP₁.2 i) (FP₂.2 i)).2 := by
      simpa [FP₁, FP₂, mul_factored_Paulis, scale_factored_Pauli, mul_Pauli1_tuples] using
        congrArg (fun fp => fp.2 i) hmul
    rw [show (Pauli_toBinSympPauli (P₁ * P₂)).1 i =
        (Z2Z2_Pauli_equiv.symm ((foldPauli.symm (P₁ * P₂)).2 i)).1 by
          rfl]
    rw [hi]
    simpa [Pauli_toBinSympPauli, PauliGroup.map, FP₁, FP₂] using
      congrArg Prod.fst (local_mul_Pauli_toBinSymp (FP₁.2 i) (FP₂.2 i))
  · have hi : (foldPauli.symm (P₁ * P₂)).2 i = (mul_Pauli1 (FP₁.2 i) (FP₂.2 i)).2 := by
      simpa [FP₁, FP₂, mul_factored_Paulis, scale_factored_Pauli, mul_Pauli1_tuples] using
        congrArg (fun fp => fp.2 i) hmul
    rw [show (Pauli_toBinSympPauli (P₁ * P₂)).2 i =
        (Z2Z2_Pauli_equiv.symm ((foldPauli.symm (P₁ * P₂)).2 i)).2 by
          rfl]
    rw [hi]
    simpa [Pauli_toBinSympPauli, PauliGroup.map, FP₁, FP₂] using
      congrArg Prod.snd (local_mul_Pauli_toBinSymp (FP₁.2 i) (FP₂.2 i))

lemma symplecticProd_succ {n : ℕ} (bp₁ bp₂ : BinSympPauli (n + 1)) :
    symplecticProd bp₁ bp₂ =
      ((bp₁.1 0) * (bp₂.2 0) + (bp₁.2 0) * (bp₂.1 0)) +
        symplecticProd (Fin.tail bp₁.1, Fin.tail bp₁.2) (Fin.tail bp₂.1, Fin.tail bp₂.2) := by
  unfold symplecticProd dotProduct
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  simp [Fin.tail]
  abel_nf

lemma anticommute_eq_symplecticBool {n : ℕ} (bp₁ bp₂ : BinSympPauli n) :
    anticommute (BinSympPauli_toPauli bp₁) (BinSympPauli_toPauli bp₂) =
      Bool.ofNat (symplecticProd bp₁ bp₂).val := by
  induction n with
  | zero =>
      simp [anticommute, anticommuteₘ, symplecticProd, dotProduct]
  | succ n ih =>
      rcases bp₁ with ⟨x₁, z₁⟩
      rcases bp₂ with ⟨x₂, z₂⟩
      have hmap₁ : PauliGroup.map (BinSympPauli_toPauli (x₁, z₁)) = fun i => Z2Z2_Pauli_equiv (x₁ i, z₁ i) := by
        simpa using PauliGroup.map_BinSympPauli_toPauli (x₁, z₁)
      have hmap₂ : PauliGroup.map (BinSympPauli_toPauli (x₂, z₂)) = fun i => Z2Z2_Pauli_equiv (x₂ i, z₂ i) := by
        simpa using PauliGroup.map_BinSympPauli_toPauli (x₂, z₂)
      have htail₁ :
          Fin.tail (fun i => Z2Z2_Pauli_equiv (x₁ i, z₁ i)) =
            fun i => Z2Z2_Pauli_equiv (Fin.tail x₁ i, Fin.tail z₁ i) := by
        funext i
        simp [Fin.tail]
      have htail₂ :
          Fin.tail (fun i => Z2Z2_Pauli_equiv (x₂ i, z₂ i)) =
            fun i => Z2Z2_Pauli_equiv (Fin.tail x₂ i, Fin.tail z₂ i) := by
        funext i
        simp [Fin.tail]
      rw [anticommute, hmap₁, hmap₂, anticommuteₘ, htail₁, htail₂]
      have htail :=
        ih (Fin.tail x₁, Fin.tail z₁) (Fin.tail x₂, Fin.tail z₂)
      rw [show
          anticommuteₘ (fun i => Z2Z2_Pauli_equiv (Fin.tail x₁ i, Fin.tail z₁ i))
              (fun i => Z2Z2_Pauli_equiv (Fin.tail x₂ i, Fin.tail z₂ i)) =
            anticommute (BinSympPauli_toPauli (Fin.tail x₁, Fin.tail z₁))
              (BinSympPauli_toPauli (Fin.tail x₂, Fin.tail z₂)) by
              rw [anticommute, PauliGroup.map_BinSympPauli_toPauli, PauliGroup.map_BinSympPauli_toPauli],
        htail]
      simpa [symplecticProd_succ] using
        (local_anticommute_xor_tail
          (x₁ 0) (z₁ 0) (x₂ 0) (z₂ 0)
          (symplecticProd (Fin.tail x₁, Fin.tail z₁) (Fin.tail x₂, Fin.tail z₂)))

lemma symplecticProd_comm {n : ℕ} (bp₁ bp₂ : BinSympPauli n) :
    symplecticProd bp₁ bp₂ = symplecticProd bp₂ bp₁ := by
  unfold symplecticProd
  rw [show bp₁.2 ⬝ᵥ bp₂.1 = bp₂.1 ⬝ᵥ bp₁.2 by simpa using dotProduct_comm bp₁.2 bp₂.1]
  rw [show bp₁.1 ⬝ᵥ bp₂.2 = bp₂.2 ⬝ᵥ bp₁.1 by simpa using dotProduct_comm bp₁.1 bp₂.2]
  rw [add_comm]

lemma BinSympPauli_toPauli_commute_iff_symplecticProd_zero {n : ℕ} (bp₁ bp₂ : BinSympPauli n) :
    commute (BinSympPauli_toPauli bp₁) (BinSympPauli_toPauli bp₂) ↔
      symplecticProd bp₁ bp₂ = 0 := by
  -- The commutativity of Pauli group elements is equivalent to the symplectic product being zero.
  unfold commute; simp [anticommute_eq_symplecticBool];
  cases h : symplecticProd bp₁ bp₂ ; simp_all +decide [ Bool.ofNat ]

theorem commutes_of_sympProd_zero {n : ℕ} {bp₁ bp₂ : BinSympPauli n}
    (h_prod : symplecticProd bp₁ bp₂ = 0) : commute (BinSympPauli_toPauli bp₁) (BinSympPauli_toPauli bp₂) := by
  exact (BinSympPauli_toPauli_commute_iff_symplecticProd_zero _ _).2 h_prod


structure BinSympMatrix (k n : ℕ) where
  X : Matrix (Fin k) (Fin n) (ZMod 2)
  Z : Matrix (Fin k) (Fin n) (ZMod 2)

def BinSympMatrix.row {n k : ℕ} (bsm : BinSympMatrix k n) (r : Fin k) : BinSympPauli n :=
  (bsm.X r, bsm.Z r)

def BinSympMatrix.rowProd {n k : ℕ} (bsm : BinSympMatrix k n) (r₁ r₂ : Fin k) : (ZMod 2) :=
  symplecticProd (bsm.row r₁) (bsm.row r₂)

def BinSympMatrix.isCommuting {n k : ℕ} (bsm : BinSympMatrix k n) : Prop :=
  ∀ r₁ r₂, bsm.rowProd r₁ r₂ = 0

def BinSympMatrix.toStabSet {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) : NormalizedStabSet n where
  stabs := Finset.image (fun i => BinSympPauli_toPauli (bsm.row i)) Finset.univ
  comm := by
    simp_rw [Finset.mem_image]
    rintro s₁ ⟨r₁, ⟨_, rfl⟩⟩ s₂ ⟨r₂, ⟨_, rfl⟩⟩
    apply commutes_of_sympProd_zero (h_comm _ _)
  norm := by
    simp_rw [Finset.mem_image]
    rintro s ⟨r₁, ⟨_, rfl⟩⟩
    unfold PauliGroup.normalized PauliGroup.phase
    simp only [BinSympPauli_toPauli, Equiv.symm_apply_apply]

abbrev BinSympMatrix.stabClosure {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) :
    Subgroup ↥(PauliGroup_group n) :=
  Subgroup.closure (SetLike.coe (bsm.toStabSet h_comm).stabs)

def StabCode_of_BinSympMatrix {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (h_minus : negIdPauli n ∉ bsm.stabClosure h_comm) : StabCode n :=
  StabCode_of_StabSet (bsm.toStabSet h_comm) h_minus

def BinSympMatrix.generators {n r : ℕ} (B : BinSympMatrix r n) (h_comm : B.isCommuting)
    (h_minus : negIdPauli n ∉ B.stabClosure h_comm) :
    (StabCode_of_BinSympMatrix B h_comm h_minus).Generators r where
  gen i := BinSympPauli_toPauli (B.row i)
  closure_eq := by
    classical
    change _ = Subgroup.closure (SetLike.coe (B.toStabSet h_comm).stabs)
    congr 1
    ext x
    simp [BinSympMatrix.toStabSet]

instance {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) :
    IsMulCommutative (bsm.stabClosure h_comm) := by
  change IsMulCommutative (Subgroup.closure (SetLike.coe (bsm.toStabSet h_comm).stabs))
  infer_instance

instance {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) :
    IsMulCommutative ↥(bsm.stabClosure h_comm) := by
  infer_instance

lemma BinSympPauli_toPauli_mul_self_eq_one {n : ℕ} (bp : BinSympPauli n) :
    BinSympPauli_toPauli bp * BinSympPauli_toPauli bp = 1 := by
  have hnorm : PauliGroup.normalized (BinSympPauli_toPauli bp) := by
    unfold PauliGroup.normalized PauliGroup.phase BinSympPauli_toPauli
    simp
  have hself : (BinSympPauli_toPauli bp : PauliGroup_group n)⁻¹ = BinSympPauli_toPauli bp :=
    PauliGroup.norm_self_inv _ hnorm
  calc
    BinSympPauli_toPauli bp * BinSympPauli_toPauli bp =
        BinSympPauli_toPauli bp * (BinSympPauli_toPauli bp)⁻¹ := by rw [hself]
    _ = 1 := by simp

def BinSympMatrix.rowStabElem {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) (i : Fin k) :
    ↥(bsm.stabClosure h_comm) :=
  ⟨BinSympPauli_toPauli (bsm.row i), by
    classical
    unfold BinSympMatrix.stabClosure BinSympMatrix.toStabSet
    apply Subgroup.subset_closure
    exact
      (Finset.mem_image.2
        ⟨i, Finset.mem_univ i, rfl⟩ :
          BinSympPauli_toPauli (bsm.row i) ∈
            Finset.image (fun j : Fin k => BinSympPauli_toPauli (bsm.row j)) Finset.univ)⟩

@[simp]
lemma BinSympMatrix.rowStabElem_coe {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) (i : Fin k) :
    ((bsm.rowStabElem h_comm i : bsm.stabClosure h_comm) : ↥(PauliGroup_group n)) =
      BinSympPauli_toPauli (bsm.row i) := rfl

@[simp]
lemma BinSympMatrix.rowStabElem_mul_self_eq_one {n k : ℕ} (bsm : BinSympMatrix k n)
    (h_comm : bsm.isCommuting) (i : Fin k) :
    bsm.rowStabElem h_comm i * bsm.rowStabElem h_comm i = 1 := by
  apply Subtype.ext
  simp [BinSympPauli_toPauli_mul_self_eq_one]

noncomputable def BinSympMatrix.rowProductSub {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind : Fin k → ZMod 2) : ↥(bsm.stabClosure h_comm) :=
  letI : CommGroup ↥(bsm.stabClosure h_comm) := subgroupCarrierCommGroup (bsm.stabClosure h_comm)
  Finset.univ.prod (fun i => if ind i = 1 then bsm.rowStabElem h_comm i else (1 : ↥(bsm.stabClosure h_comm)))

def BinSympMatrix.rowProduct {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind : Fin k → ZMod 2) : ↥(PauliGroup_group n) :=
  (bsm.rowProductSub h_comm ind : ↥(PauliGroup_group n))

@[simp]
lemma BinSympMatrix.rowProduct_zero {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) :
    bsm.rowProduct h_comm (fun _ => (0 : ZMod 2)) = 1 := by
  letI : CommGroup ↥(bsm.stabClosure h_comm) := subgroupCarrierCommGroup (bsm.stabClosure h_comm)
  have hsub : bsm.rowProductSub h_comm (fun _ => (0 : ZMod 2)) = 1 := by
    unfold BinSympMatrix.rowProductSub
    simp only [zero_ne_one, ↓reduceIte]
    rw [Finset.prod_const]
    simp only [Finset.card_univ, Fintype.card_fin]
    exact one_pow k
  exact congrArg Subtype.val hsub

lemma BinSympMatrix.rowProduct_single {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting) (i : Fin k) :
    bsm.rowProduct h_comm (Pi.single i (1 : ZMod 2)) = BinSympPauli_toPauli (bsm.row i) := by
  letI : CommGroup ↥(bsm.stabClosure h_comm) := subgroupCarrierCommGroup (bsm.stabClosure h_comm)
  have hsub : bsm.rowProductSub h_comm (Pi.single i (1 : ZMod 2)) = bsm.rowStabElem h_comm i := by
    unfold BinSympMatrix.rowProductSub
    simp only [Pi.single_apply]
    rw [show
      (fun x : Fin k =>
        if (if x = i then (1 : ZMod 2) else 0) = 1 then bsm.rowStabElem h_comm x else 1) =
      (fun x : Fin k => if x = i then bsm.rowStabElem h_comm x else 1) from by
        funext x
        by_cases h : x = i <;> simp [h]]
    exact Fintype.prod_ite_eq' i (fun x => bsm.rowStabElem h_comm x)
  exact congrArg Subtype.val hsub

lemma BinSympMatrix.rowProductSub_add {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind₁ ind₂ : Fin k → ZMod 2) :
    bsm.rowProductSub h_comm (fun i => ind₁ i + ind₂ i) =
      bsm.rowProductSub h_comm ind₁ * bsm.rowProductSub h_comm ind₂ := by
  letI : CommGroup ↥(bsm.stabClosure h_comm) := subgroupCarrierCommGroup (bsm.stabClosure h_comm)
  unfold BinSympMatrix.rowProductSub
  calc
    (∏ i, if (fun i => ind₁ i + ind₂ i) i = 1 then bsm.rowStabElem h_comm i else 1)
        = ∏ i, ((if ind₁ i = 1 then bsm.rowStabElem h_comm i else 1) *
            (if ind₂ i = 1 then bsm.rowStabElem h_comm i else 1)) := by
          apply Finset.prod_congr rfl
          intro i _
          change (if ind₁ i + ind₂ i = 1 then bsm.rowStabElem h_comm i else 1) =
            (if ind₁ i = 1 then bsm.rowStabElem h_comm i else 1) *
              (if ind₂ i = 1 then bsm.rowStabElem h_comm i else 1)
          rcases Fin.exists_fin_two.mp ⟨ind₁ i, rfl⟩ with h₁ | h₁
          · rcases Fin.exists_fin_two.mp ⟨ind₂ i, rfl⟩ with h₂ | h₂
            · rw [h₁, h₂]
              change (1 : ↥(bsm.stabClosure h_comm)) = 1 * 1
              simp
            · rw [h₁, h₂]
              change bsm.rowStabElem h_comm i = 1 * bsm.rowStabElem h_comm i
              simp
          · rcases Fin.exists_fin_two.mp ⟨ind₂ i, rfl⟩ with h₂ | h₂
            · rw [h₁, h₂]
              change bsm.rowStabElem h_comm i = bsm.rowStabElem h_comm i * 1
              simp
            · rw [h₁, h₂]
              change (1 : ↥(bsm.stabClosure h_comm)) =
                bsm.rowStabElem h_comm i * bsm.rowStabElem h_comm i
              exact (BinSympMatrix.rowStabElem_mul_self_eq_one bsm h_comm i).symm
    _ = (∏ i, if ind₁ i = 1 then bsm.rowStabElem h_comm i else 1) *
          ∏ i, if ind₂ i = 1 then bsm.rowStabElem h_comm i else 1 := by
          exact Finset.prod_mul_distrib

lemma BinSympMatrix.rowProduct_add {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind₁ ind₂ : Fin k → ZMod 2) :
    bsm.rowProduct h_comm (fun i => ind₁ i + ind₂ i) =
      bsm.rowProduct h_comm ind₁ * bsm.rowProduct h_comm ind₂ := by
  simpa [BinSympMatrix.rowProduct] using congrArg Subtype.val
    (BinSympMatrix.rowProductSub_add bsm h_comm ind₁ ind₂)

lemma BinSympMatrix.rowProduct_self_mul_eq_one {n k : ℕ} (bsm : BinSympMatrix k n)
    (h_comm : bsm.isCommuting) (ind : Fin k → ZMod 2) :
    bsm.rowProduct h_comm ind * bsm.rowProduct h_comm ind = 1 := by
  convert bsm.rowProduct_add h_comm ind ind using 1;
  · rw [ ← bsm.rowProduct_add h_comm ind ind ];
  · rw [ ← bsm.rowProduct_add h_comm ind ind ];
    rw [ show ( fun i => ind i + ind i ) = fun _ => 0 from funext fun _ => by simp +decide [ ← two_mul ] ] ; exact Eq.symm ( bsm.rowProduct_zero h_comm )

lemma BinSympMatrix.rowProduct_inv_eq_self {n k : ℕ} (bsm : BinSympMatrix k n)
    (h_comm : bsm.isCommuting) (ind : Fin k → ZMod 2) :
    (bsm.rowProduct h_comm ind)⁻¹ = bsm.rowProduct h_comm ind :=
  inv_eq_self_of_mul_self_eq_one (BinSympMatrix.rowProduct_self_mul_eq_one bsm h_comm ind)

set_option maxHeartbeats 0 in
lemma BinSympMatrix.rowProduct_binaryImage {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (ind : Fin k → ZMod 2) :
    Pauli_toBinSympPauli (bsm.rowProduct h_comm ind) = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind) := by
  have h_sum : ∀ (ind : Fin k → ZMod 2),
      Pauli_toBinSympPauli (bsm.rowProduct h_comm ind) =
        ∑ i, ind i • Pauli_toBinSympPauli (BinSympPauli_toPauli (bsm.row i)) := by
    intro ind
    induction' ind using Pi.single_induction with i ind ih
    · simp +decide [BinSympMatrix.rowProduct_zero]
      convert Pauli_toBinSympPauli_one
      convert BinSympMatrix.rowProduct_zero bsm h_comm
    · have h_sum :
          Pauli_toBinSympPauli (bsm.rowProduct h_comm (i + ind)) =
            Pauli_toBinSympPauli (bsm.rowProduct h_comm i) +
              Pauli_toBinSympPauli (bsm.rowProduct h_comm ind) := by
        convert Pauli_to_BinSymp_correct _ _ using 1
        exact congr_arg _ (BinSympMatrix.rowProduct_add _ _ _ _)
      simp_all +decide [add_smul, Finset.sum_add_distrib]
    · rename_i i m
      fin_cases m
      · change
          Pauli_toBinSympPauli
            (bsm.rowProduct h_comm (Pi.single (M := fun _ : Fin k => ZMod 2) i (0 : ZMod 2))) =
            ∑ i_1,
              (Pi.single (M := fun _ : Fin k => ZMod 2) i (0 : ZMod 2)) i_1 •
                Pauli_toBinSympPauli (BinSympPauli_toPauli (bsm.row i_1))
        have hzero : Pi.single (M := fun _ : Fin k => ZMod 2) i (0 : ZMod 2) =
            fun _ => (0 : ZMod 2) := by
          ext j
          by_cases h : j = i <;> simp [Pi.single_apply, h]
        rw [hzero, BinSympMatrix.rowProduct_zero]
        simp [Pauli_toBinSympPauli_one]
      · change
          Pauli_toBinSympPauli
            (bsm.rowProduct h_comm (Pi.single (M := fun _ : Fin k => ZMod 2) i (1 : ZMod 2))) =
            ∑ i_1,
              (Pi.single (M := fun _ : Fin k => ZMod 2) i (1 : ZMod 2)) i_1 •
                Pauli_toBinSympPauli (BinSympPauli_toPauli (bsm.row i_1))
        rw [BinSympMatrix.rowProduct_single]
        simp [Pauli_toBinSympPauli_BinSympPauli_toPauli]
  ext i
  simp +decide [h_sum, Matrix.mulVec, dotProduct]
  · simp +decide [mul_comm, Finset.sum_apply, BinSympMatrix.row]
    simp +decide [Prod.fst_sum]
  · simp_all +decide [Finset.sum_apply, dotProduct, Matrix.mulVec, Finset.mul_sum _ _ _]
    simp +decide [mul_comm, Finset.sum_apply, Prod.snd_sum]
    rfl

lemma BinSympMatrix.selectedRows_sum_eq_mulVec {n k : ℕ} (bsm : BinSympMatrix k n)
    (ind : Fin k → ZMod 2) :
    Finset.univ.sum (fun i => if ind i = 1 then bsm.row i else 0) =
      (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind) := by
  ext j
  · have hpair :
        (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).1 j =
          Finset.univ.sum (fun i => if ind i = 1 then bsm.X i j else 0) := by
      induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha ih =>
          by_cases hia : ind a = 1
          · simpa [ha, hia, BinSympMatrix.row] using ih
          · simpa [ha, hia, BinSympMatrix.row] using ih
    calc
      (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).1 j
          = Finset.univ.sum (fun i => if ind i = 1 then bsm.X i j else 0) := hpair
      _ = Finset.univ.sum (fun i => bsm.X i j * ind i) := by
            rw [sum_univ_if_eq_one]
      _ = (bsm.X.transpose.mulVec ind) j := by
            simp [Matrix.mulVec, dotProduct, mul_comm]
      _ = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind).1 j := by
            rfl
  · have hpair :
        (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).2 j =
          Finset.univ.sum (fun i => if ind i = 1 then bsm.Z i j else 0) := by
      induction (Finset.univ : Finset (Fin k)) using Finset.induction_on with
      | empty =>
          simp
      | @insert a s ha ih =>
          by_cases hia : ind a = 1
          · simpa [ha, hia, BinSympMatrix.row] using ih
          · simpa [ha, hia, BinSympMatrix.row] using ih
    calc
      (Finset.univ.sum fun i => if ind i = 1 then bsm.row i else 0).2 j
          = Finset.univ.sum (fun i => if ind i = 1 then bsm.Z i j else 0) := hpair
      _ = Finset.univ.sum (fun i => bsm.Z i j * ind i) := by
            rw [sum_univ_if_eq_one]
      _ = (bsm.Z.transpose.mulVec ind) j := by
            simp [Matrix.mulVec, dotProduct, mul_comm]
      _ = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind).2 j := by
            rfl

theorem BinSympCode_stab_eq_rowProduct {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (h_minus : negIdPauli n ∉ bsm.stabClosure h_comm) (s : ↥(PauliGroup_group n)) :
    s ∈ (StabCode_of_BinSympMatrix bsm h_comm h_minus).stabs ↔ ∃ ind, bsm.rowProduct h_comm ind = s := by
  constructor
  · revert s
    unfold StabCode_of_BinSympMatrix StabCode_of_StabSet BinSympMatrix.toStabSet
    simp only
    apply Subgroup.closure_induction
    · intro x hx
      simp only [Finset.mem_coe, Finset.mem_image] at hx
      rcases hx with ⟨i, _, rfl⟩
      exact ⟨Pi.single i (1 : ZMod 2), BinSympMatrix.rowProduct_single bsm h_comm i⟩
    · exact ⟨0, BinSympMatrix.rowProduct_zero bsm h_comm⟩
    · intro x y _ _ hx hy
      rcases hx with ⟨ind₁, rfl⟩
      rcases hy with ⟨ind₂, rfl⟩
      exact ⟨fun i => ind₁ i + ind₂ i, BinSympMatrix.rowProduct_add bsm h_comm ind₁ ind₂⟩
    · intro x _ hx
      rcases hx with ⟨ind, rfl⟩
      exact ⟨ind, (BinSympMatrix.rowProduct_inv_eq_self bsm h_comm ind).symm⟩
  · rintro ⟨ind, rfl⟩
    simp [BinSympMatrix.rowProduct, BinSympMatrix.stabClosure, StabCode_of_BinSympMatrix,
      StabCode_of_StabSet]

theorem BinSympCode_stab_eq_rowSpace {n k : ℕ} (bsm : BinSympMatrix k n) (h_comm : bsm.isCommuting)
    (h_minus : negIdPauli n ∉ bsm.stabClosure h_comm) (s : ↥(PauliGroup_group n)) :
    s ∈ (StabCode_of_BinSympMatrix bsm h_comm h_minus).stabs ↔
      ∃ ind, bsm.rowProduct h_comm ind = s ∧
        Pauli_toBinSympPauli s = (bsm.X.transpose.mulVec ind, bsm.Z.transpose.mulVec ind) := by
  rw [BinSympCode_stab_eq_rowProduct]
  constructor
  · rintro ⟨ind, rfl⟩
    exact ⟨ind, rfl, BinSympMatrix.rowProduct_binaryImage bsm h_comm ind⟩
  · rintro ⟨ind, hs, _⟩
    exact ⟨ind, hs⟩

end
