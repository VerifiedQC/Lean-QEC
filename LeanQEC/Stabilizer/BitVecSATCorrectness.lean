import LeanQEC.Stabilizer.BitVecSat
import LeanQEC.Stabilizer.CSS
import LeanQEC.Stabilizer.LinAlgToBool


instance {n : Nat} : Coe ((Fin n) → ZMod 2) ((Fin n) → Bool) where
  coe f := fun i => (f i).val == 1

def vec_to_BitVec {j : ℕ} (r : (Fin j) → (ZMod 2)) : BitVec j := BitVec.ofFnLE r




--for Fin j → Fin n
def vec_to_BitVec' {j n : ℕ} (r : (Fin j) → (Fin n)) : BitVec (j * (Nat.clog 2 n)) :=
  match j with
  | 0 => (BitVec.zero 0).cast (by rw [zero_mul])
  | 1 => (r 0)
  | j' + 1 => ((r ⟨j', Nat.lt_succ_self _⟩ : BitVec (Nat.clog 2 n)).append (vec_to_BitVec' (fun i : Fin j' => r ⟨i, by simp⟩))).cast (by rw [Nat.succ_mul, Nat.add_comm])


--terrible?
def BitVec.appendList {i j : ℕ} (f : (Fin i) → (BitVec j)) : BitVec (i * j) :=
  match i with
  | 0 => (BitVec.zero 0).cast (by rw [MulZeroClass.zero_mul])
  | 1 => (f 0).cast (by rw [one_mul])
  | i' + 1 => (((f ⟨i', Nat.lt_succ_self _⟩).append (BitVec.appendList (fun (j : Fin i') => f ⟨j, by simp⟩)))).cast (by rw [Nat.succ_mul, Nat.add_comm])

def Matrix.toBitVecs {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) : (Fin i) → (BitVec j) :=
  fun a => vec_to_BitVec (M a)


def flatten_matrix {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) : BitVec (i * j) :=
  BitVec.appendList M.toBitVecs

--function transforming error vector with limited support into index vector
def index_vec {n k : ℕ} (x : Fin n → ZMod 2) (hx : hammingNorm x = k) : Fin k → Fin n :=
  let S := Finset.univ.filter (fun j : Fin n => x j ≠ 0);
  let I : Fin k → Fin n := fun j =>
        (S.orderEmbOfFin (by
          rw [←hx]
          simp [S, hammingNorm]
        ) j)
  I

lemma index_vec_eq_one_of_exists {n k : ℕ} {x : Fin n → ZMod 2} {hx : hammingNorm x = k}
  {y : Fin k} {i : Fin n}
  (h_ind : index_vec x hx y = i) :
  x i ≠ 0 := sorry


--def T : Matrix (Fin 2) (Fin 2) (ZMod 2) := !![1, 1; 0, 1]
--#eval! flatten_matrix T -- evaluates to 11: successully flattened
--#eval! (flatten_matrix T)[1]


lemma vec_to_BitVec'_correct {i n : ℕ} {r : (Fin i) → (Fin n)} (j : Fin i) :
  (vec_to_BitVec' r).extractLsb' (j * (Nat.clog 2 n)) (Nat.clog 2 n) = r j := sorry




lemma vec_to_BitVec_correct {j : ℕ} (r : (Fin j) → (ZMod 2)) (i : Fin j) : (vec_to_BitVec r)[i]! = ((r i).val == 1) := by
  simp [vec_to_BitVec]


lemma flatten_matrix_correct {i j : ℕ} (M : Matrix (Fin i) (Fin j) (ZMod 2)) (r : Fin i) (c : Fin j) :
  (flatten_matrix M)[(r * i) + c]! = ((M r c).val == 1) := sorry


lemma loc_constraints_ascent
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n)
  (hl : ∀ (i : Fin n), loc_constraints_ith locs errs i)
 : loc_constraints locs errs := sorry

lemma loc_constraints_descent
  {n nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (errs : BitVec n)
  (hl : loc_constraints locs errs)
  (i : Fin n)
  : loc_constraints_ith locs errs i := sorry

lemma loc_constraints_ith_jth_aux_correct
  {nlog k : ℕ}
  (locs : BitVec (k * nlog))
  (i j : ℕ)
  : loc_constraints_ith_jth_aux locs i j =  (∃ l : Fin k, locs.extractLsb' (l * nlog) nlog = i) := sorry

lemma fin_to_bitvec_clog {n : ℕ} {x : Fin n} : (x : BitVec (Nat.clog 2 n)) = BitVec.ofNat (Nat.clog 2 n) x := by
  simp

lemma BitVec.ofNat_clog_eq_iff {n : ℕ} {x y : Fin n} :
  BitVec.ofNat (Nat.clog 2 n) x = BitVec.ofNat (Nat.clog 2 n) y ↔ x = y := sorry

lemma loc_constraints_of_index {n k : ℕ} (x : Fin n → (ZMod 2)) (hx : hammingNorm x = k) :
  loc_constraints (vec_to_BitVec' (index_vec x hx)) (vec_to_BitVec x) := by
  apply loc_constraints_ascent
  intro i
  unfold loc_constraints_ith
  rw [loc_constraints_ith_jth_aux_correct]
  by_cases h : (x i = 0)
  · simp [vec_to_BitVec, h]
    intro y
    rw [vec_to_BitVec'_correct, fin_to_bitvec_clog, BitVec.ofNat_clog_eq_iff]
    intro h_f
    apply absurd h
    apply index_vec_eq_one_of_exists h_f
  sorry





def row_inner_product_correct {k n : ℕ} (M : Matrix (Fin k) (Fin n) (ZMod 2)) (x : Fin n → (ZMod 2)) (r : Fin k):
  row_inner_product (flatten_matrix M) (vec_to_BitVec x) r = ((M.row r) ⬝ᵥ x == 1) := sorry

lemma parity_constraints_descent {stabdim n : ℕ} {stabs : BitVec (stabdim * n)} {errs : BitVec n} {r : Fin stabdim} (hpc : parity_constraints stabs errs) :
  !(row_inner_product stabs errs r) := sorry

lemma parity_constraints_ascent {stabdim n : ℕ} {stabs : BitVec (stabdim * n)}
{errs : BitVec n} (hpaux : ∀ (r : Fin stabdim), !(row_inner_product stabs errs r))
 : parity_constraints stabs errs := sorry

lemma parity_constraints_correct {k n : ℕ} {M : Matrix (Fin k) (Fin n) (ZMod 2)}
  {x : Fin n → ZMod 2} :
  parity_constraints (flatten_matrix M) (vec_to_BitVec x) ↔ x ∈ LinearMap.ker M.toLin' := by
  rw [LinearMap.mem_ker]
  have pc_correct_aux : ∀ (i : Fin k),
  !row_inner_product (flatten_matrix M) (vec_to_BitVec x) i ↔ (M.mulVec x) i = 0 := sorry
  rw [Matrix.toLin'_apply]
  constructor
  · intro hpar
    ext i
    apply (pc_correct_aux i).1
    apply parity_constraints_descent hpar
  intro hmul
  apply parity_constraints_ascent
  intro r
  apply (pc_correct_aux r).2
  rw [hmul]
  simp only [Pi.zero_apply]

lemma rowspace_constraints_descent {kerdim n} {ker : BitVec (kerdim * n)}
{errs : BitVec n} (r : Fin kerdim) (hr : row_inner_product ker errs r)
: rowspace_constraints ker errs := sorry


lemma rowspace_constraints_ascent {kerdim n} {ker : BitVec (kerdim * n)}
{errs : BitVec n} (hconstr : rowspace_constraints ker errs)
: ∃ (r : Fin kerdim), row_inner_product ker errs r := sorry


lemma rowspace_constraints_correct {k n : ℕ}
  {M₁ : Matrix (Fin k₁) (Fin n) (ZMod 2)}
  {M₂ : Matrix (Fin k₂) (Fin n) (ZMod 2)}
  (hK : M₂.rowSpace = (LinearMap.ker (M₁.toLin')))
  {x : Fin n → ZMod 2} :
  rowspace_constraints (flatten_matrix M₂) (vec_to_BitVec x) ↔ x ∉ M₁.rowSpace := by
  rw [not_mem_rowspace_iff_exists_mem_ker]
  constructor
  · intro hrc
    rcases rowspace_constraints_ascent hrc with ⟨r, hrp⟩
    refine ⟨M₂.row r, ⟨?_, ?_⟩⟩
    · rw [←hK]
      exact Matrix.row_mem_rowSpace
    rw [row_inner_product_correct] at hrp
    simp only [beq_iff_eq] at hrp
    assumption
  rintro ⟨y, ⟨hy₁, hy₂⟩⟩
  rw [←hK] at hy₁
  obtain ⟨s, hs⟩ := exists_row_of_exists_mem_rowspace_non_orth hy₁ hy₂
  apply rowspace_constraints_descent s
  rwa [row_inner_product_correct, beq_iff_eq]













def kergen_correct {a b n : ℕ}
  (M : Matrix (Fin a) (Fin b) (ZMod 2))
  (gen : Fin n -> Fin b -> ZMod 2) : Prop :=
  LinearMap.ker M.toLin' =
  Submodule.span (ZMod 2) (Finset.image gen Finset.univ)

lemma min_weight_ker_not_mem_rowspace_empty
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (is_empty : ¬∃x, x ∈ LinearMap.ker H₁.toLin' /\ x ∉ H₂.rowSpace) :
  min_weight_ker_not_mem_rowspace H₁ H₂ = n + 1 := by
  unfold min_weight_ker_not_mem_rowspace at *
  simp_all +decide
  rw [show (LinearMap.ker (Matrix.toLin' H₁) : Set (Fin n → ZMod 2)).toFinset \
    (H₂.rowSpace : Set (Fin n → ZMod 2)).toFinset = ∅ from by ext x; aesop]
  simp +decide

-- property of minimum
-- if minimum is less than a certain number, then there exists a witness
lemma dist_index_some
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (dist : ℕ)
  (non_empty : ∃x, x ∈ LinearMap.ker H₁.toLin' /\ x ∉ H₂.rowSpace)
  (hdist : min_weight_ker_not_mem_rowspace H₁ H₂ < dist) :
  ∃x, x ∈ LinearMap.ker H₁.toLin' /\
    x ∉ H₂.rowSpace /\ hammingNorm x < dist := by
  contrapose! hdist
  simp_all +decide [min_weight_ker_not_mem_rowspace]
  rcases h : Finset.min (Finset.image hammingNorm
    ((LinearMap.ker H₁.toLin' : Set (Fin n → ZMod 2)).toFinset \
    (H₂.rowSpace : Set (Fin n → ZMod 2)).toFinset)) with (_ | a) <;> simp_all +decide
  · simp_all +decide [Finset.min]
    simp_all +decide [Finset.inf_eq_iInf]
    simp_all +decide [WithTop.none_eq_top, iInf]
    exact False.elim <| non_empty.choose_spec.2 <| h _ non_empty.choose_spec.1
  · have := Finset.mem_of_min h; aesop

/-
lemma dist_index_le_sound_contrapositive
  {n k₁ k₂ kersize : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (H₂_kergen : Fin kersize → Fin n → ZMod 2)
  (H₂_kergen_correct : kergen_correct H₂ H₂_kergen)
  (dist : Fin n)
  (hdist : min_weight_ker_not_mem_rowspace H₁ H₂ < dist) :
  ¬(lt_dist_sat (flatten_matrix H₁) (flatten_matrix (H₂_kergen)) dist (Nat.clog 2 n))
     := by
  let undetectable_errors : Set (Fin n → ZMod 2) :=
    LinearMap.ker H₁.toLin' \ H₂.rowSpace
  intro htest
  by_cases h_empty : undetectable_errors = ∅
  · have hmin : min_weight_ker_not_mem_rowspace H₁ H₂ = n + 1 := by
      apply min_weight_ker_not_mem_rowspace_empty H₁ H₂
      intro h_nonempty
      rcases h_nonempty with ⟨x, hxker, hxrow⟩
      have : x ∈ undetectable_errors := ⟨hxker, hxrow⟩
      simp [h_empty] at this
    rw [hmin] at hdist
    exact absurd hdist (not_lt_of_ge (le_trans (Nat.le_of_lt dist.isLt) (Nat.le_succ n)))
  · have h_nonempty : ∃ x, x ∈ LinearMap.ker H₁.toLin' /\ x ∉ H₂.rowSpace := by
      rcases Set.nonempty_iff_ne_empty.mpr h_empty with ⟨x, hx⟩
      exact ⟨x, hx.1, hx.2⟩
    rcases dist_index_some H₁ H₂ dist h_nonempty hdist with
      ⟨x, ker_x, rowspace_x, hamming_x⟩
    have hx_ne_zero : x ≠ 0 := by
      intro hx0
      apply rowspace_x
      simpa [hx0] using (show (0 : Fin n → ZMod 2) ∈ H₂.rowSpace from Submodule.zero_mem _)
    let S : Finset (Fin n) := Finset.univ.filter fun j : Fin n => x j ≠ 0
    have hS_card : S.card = hammingNorm x := by
      simp [S, hammingNorm]
    have hS_le : S.card ≤ dist - 1 := by
      rw [hS_card]
      exact Nat.le_sub_one_of_lt hamming_x
    have hS_nonempty : S.Nonempty := by
      have hS_pos : 0 < S.card := by
        rw [hS_card]
        simpa using (hammingNorm_pos_iff.2 hx_ne_zero)
      exact Finset.card_pos.mp hS_pos

    let I : Fin (S.card) → Fin n := fun j =>
        (S.orderEmbOfFin rfl j)
    have h_exists_iff :
        ∀ i : Fin n, (∃ j , I j = i) ↔ i ∈ S := by
      intro i
      constructor
      · rintro ⟨j, hIj⟩
        rw [←hIj]
        simp only [Finset.orderEmbOfFin_mem, I]
      · intro hiS
        let j : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨i, hiS⟩
        use j
        have hsub : S.orderIsoOfFin rfl j = ⟨i, hiS⟩ := by
          simpa [j] using (S.orderIsoOfFin rfl).apply_symm_apply ⟨i, hiS⟩
        have hj_eq : S.orderEmbOfFin rfl j = i := by
          simpa using congrArg Subtype.val hsub
        simp only [hj_eq, I]

    have hI_to_vec : I_to_vec n S.card I = x := by
      funext i
      by_cases hiS : i ∈ S
      · have hex : ∃ j : ℕ, j < (dist : ℕ) - 1 ∧ I j = i := (h_exists_iff i).2 hiS
        have hxi_ne : x i ≠ 0 := by
          simpa [S] using hiS
        have hxi : x i = 1 := by
          rcases Fin.exists_fin_two.mp ⟨x i, rfl⟩ with hxi | hxi
          · exact absurd hxi hxi_ne
          · exact hxi
        rw [I_to_vec]
        simp [hex, hxi]
      · have hnot : ¬ ∃ j : ℕ, j < (dist : ℕ) - 1 ∧ I j = i := by
          exact fun h => hiS ((h_exists_iff i).1 h)
        have hxi : x i = 0 := by
          by_contra hxi_ne
          exact hiS (by simpa [S] using hxi_ne)
        rw [I_to_vec]
        simp [hnot, hxi]
    have hindex : is_index_bool I (dist - 1) n = true := by
      unfold is_index_bool
      rw [Bool.and_eq_true, Finset.fold_true_to_prop, Finset.fold_true_to_prop]
      constructor
      · intro j hjdist
        by_cases hjS : j < S.card
        · simpa [I, hjS] using (S.orderEmbOfFin rfl ⟨j, hjS⟩).isLt
        · simpa [I, hjS] using (S.max' hS_nonempty).isLt
      · intro j hj
        by_cases hnext : j + 1 < S.card
        · have hjS : j < S.card := lt_trans (Nat.lt_succ_self j) hnext
          have : S.orderEmbOfFin rfl ⟨j, hjS⟩ ≤ S.orderEmbOfFin rfl ⟨j + 1, hnext⟩ := by
            exact (S.orderEmbOfFin rfl).monotone (show (⟨j, hjS⟩ : Fin S.card) ≤ ⟨j + 1, hnext⟩ from Nat.le_succ _)
          simpa [I, hjS, hnext] using this
        · by_cases hjS : j < S.card
          · have hmem : S.orderEmbOfFin rfl ⟨j, hjS⟩ ∈ S := by
              simp
            have : S.orderEmbOfFin rfl ⟨j, hjS⟩ ≤ S.max' hS_nonempty := by
              exact S.le_max' _ hmem
            simpa [I, hjS, hnext] using this
          · simpa [I, hjS, hnext]
    have hker_bool : mem_ker_bool k₁ n (forget H₁) (indexed_by I (dist - 1)) = true := by
      rw [forget_eq_castnat_castbool]
      exact (mem_ker_iff (M := H₁) (I := I) (d := dist - 1)).2 (by simpa [hI_to_vec] using ker_x)
    have hK : (Matrix.of H₂_kergen).rowSpace = LinearMap.ker H₂.toLin' := by
      simpa [kergen_correct, Matrix.rowSpace, Matrix.row] using H₂_kergen_correct.symm
    have hrow_bool :
        not_mem_rowspace (n - k₂) n (forget (Matrix.of H₂_kergen)) (indexed_by I (dist - 1)) = true := by
      rw [forget_eq_castnat_castbool]
      exact (not_mem_rowspace_iff (M₁ := H₂) (M₂ := Matrix.of H₂_kergen) (I := I)
        (d := dist - 1) hK).2 (by simpa [hI_to_vec] using rowspace_x)
    simpa [hindex, hker_bool, hrow_bool] using htest I
-/

theorem sat_translation_correct
  {n nlog k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero k₂] [NeZero (n - k₁)] [NeZero (n - k₂)]
  (css : CSS_pair n k₁ k₂)
  (xkergen : Fin (n - k₁) → Fin n → ZMod 2)
  (xkergen_correct : kergen_correct css.H₁ xkergen)
  (zkergen : Fin (n - k₂) → Fin n → ZMod 2)
  (zkergen_correct : kergen_correct css.H₂ zkergen)
  (dist : ℕ) :
  lt_dist_sat (flatten_matrix css.H₁) (flatten_matrix (Matrix.of xkergen)) dist nlog →
  lt_dist_sat (flatten_matrix css.H₂) (flatten_matrix (Matrix.of zkergen)) dist nlog →
  dist ≤ css.toBSM.distance (by apply NeZero.pos) := sorry
