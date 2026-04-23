import LeanQEC.Stabilizer.Basic
import LeanQEC.Stabilizer.CSS
import LeanQEC.Stabilizer.LinAlgSMT
import LeanQEC.Stabilizer.LinAlgToBool

def forget {a b : ℕ} [NeZero a] [NeZero b]
  (M : Matrix (Fin a) (Fin b) (ZMod 2)) :
  Matrix ℕ ℕ Bool :=
  Matrix.of (fun i j =>
    if i < a && j < b then
      M (Fin.ofNat a i) (Fin.ofNat b j) = 1
    else false)

lemma forget_eq_castnat_castbool {a b : ℕ} [NeZero a] [NeZero b]
  (M : Matrix (Fin a) (Fin b) (ZMod 2)) :
    forget M = M.castnat.castbool := by
  unfold forget
  ext i j; simp [Matrix.castnat, Matrix.castbool, Fin.ofNat];
  split_ifs <;> simp_all +decide [ Nat.mod_eq_of_lt ];
  rcases M ⟨ i, by linarith ⟩ ⟨ j, by linarith ⟩ with ( _ | _ | m ) <;> trivial;

def kergen_correct {a b n : ℕ}
  (M : Matrix (Fin a) (Fin b) (ZMod 2))
  (gen : Fin n -> Fin b -> ZMod 2) : Prop :=
  LinearMap.ker M.toLin' =
  Submodule.span (ZMod 2) (Finset.image gen Finset.univ)

lemma min_weight_ker_not_mem_rowspace_empty
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (H₂_kergen : Fin (n - k₂) → Fin n → ZMod 2)
  (H₂_kergen_correct : kergen_correct H₂ H₂_kergen)
  (is_empty : ¬∃x, x ∈ LinearMap.ker H₁.toLin' /\ x ∉ H₂.rowSpace) :
  min_weight_ker_not_mem_rowspace H₁ H₂ = n + 1 := by
  unfold min_weight_ker_not_mem_rowspace at *
  simp_all +decide [Set.eq_empty_iff_forall_notMem]
  rw [show (LinearMap.ker (Matrix.toLin' H₁) : Set (Fin n → ZMod 2)).toFinset \
    (H₂.rowSpace : Set (Fin n → ZMod 2)).toFinset = ∅ from by ext x; aesop]
  simp +decide

-- property of minimum
-- if minimum is less than a certain number, then there exists a witness
lemma dist_index_some
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (H₂_kergen : Fin (n - k₂) → Fin n → ZMod 2)
  (H₂_kergen_correct : kergen_correct H₂ H₂_kergen)
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

lemma dist_index_le_sound_contrapositive
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (H₂_kergen : Fin (n - k₂) → Fin n → ZMod 2)
  (H₂_kergen_correct : kergen_correct H₂ H₂_kergen)
  (dist : Fin n)
  (hdist : min_weight_ker_not_mem_rowspace H₁ H₂ < dist) :
  ¬(dist_index_le n k₁ (n - k₂)
    (forget H₁) (forget (Matrix.of H₂_kergen)) dist) := by
  let undetectable_errors : Set (Fin n → ZMod 2) :=
    LinearMap.ker H₁.toLin' \ H₂.rowSpace
  intro htest
  by_cases h_empty : undetectable_errors = ∅
  · have hmin : min_weight_ker_not_mem_rowspace H₁ H₂ = n + 1 := by
      apply min_weight_ker_not_mem_rowspace_empty H₁ H₂ H₂_kergen H₂_kergen_correct
      intro h_nonempty
      rcases h_nonempty with ⟨x, hxker, hxrow⟩
      have : x ∈ undetectable_errors := ⟨hxker, hxrow⟩
      simpa [h_empty] using this
    rw [hmin] at hdist
    exact absurd hdist (not_lt_of_ge (le_trans (Nat.le_of_lt dist.isLt) (Nat.le_succ n)))
  · have h_nonempty : ∃ x, x ∈ LinearMap.ker H₁.toLin' /\ x ∉ H₂.rowSpace := by
      rcases Set.nonempty_iff_ne_empty.mpr h_empty with ⟨x, hx⟩
      exact ⟨x, hx.1, hx.2⟩
    rcases dist_index_some H₁ H₂ H₂_kergen H₂_kergen_correct dist h_nonempty hdist with
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
    let I : ℕ → ℕ := fun j =>
      if hj : j < S.card then
        (S.orderEmbOfFin rfl ⟨j, hj⟩).val
      else
        (S.max' hS_nonempty).val
    have h_exists_iff :
        ∀ i : Fin n, (∃ j : ℕ, j < (dist : ℕ) - 1 ∧ I j = i) ↔ i ∈ S := by
      intro i
      constructor
      · rintro ⟨j, hjdist, hIj⟩
        by_cases hjS : j < S.card
        · have hi_eq : S.orderEmbOfFin rfl ⟨j, hjS⟩ = i := by
            apply Fin.ext
            simpa [I, hjS] using hIj
          simpa [hi_eq] using (S.orderEmbOfFin_mem rfl ⟨j, hjS⟩)
        · have hi_eq : S.max' hS_nonempty = i := by
            apply Fin.ext
            simpa [I, hjS] using hIj
          simpa [hi_eq] using (S.max'_mem hS_nonempty)
      · intro hiS
        let j : Fin S.card := (S.orderIsoOfFin rfl).symm ⟨i, hiS⟩
        refine ⟨j.1, lt_of_lt_of_le j.2 hS_le, ?_⟩
        have hsub : S.orderIsoOfFin rfl j = ⟨i, hiS⟩ := by
          simpa [j] using (S.orderIsoOfFin rfl).apply_symm_apply ⟨i, hiS⟩
        have hj_eq : S.orderEmbOfFin rfl j = i := by
          simpa using congrArg Subtype.val hsub
        simpa [I, j.2] using congrArg Fin.val hj_eq
    have hI_to_vec : I_to_vec n (dist - 1) I = x := by
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

lemma dist_index_le_sound
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero (n - k₂)]
  (H₁ : Matrix (Fin k₁) (Fin n) (ZMod 2))
  (H₂ : Matrix (Fin k₂) (Fin n) (ZMod 2))
  (H₂_kergen : Fin (n - k₂) → Fin n → ZMod 2)
  (H₂_kergen_correct : kergen_correct H₂ H₂_kergen)
  (dist : Fin n)
  (test_dist : dist_index_le n k₁ (n - k₂)
    (forget H₁) (forget (Matrix.of H₂_kergen)) dist) :
  dist ≤ min_weight_ker_not_mem_rowspace H₁ H₂ := by
  by_contra
  suffices: ¬(dist_index_le n k₁ (n - k₂) (forget H₁) (forget (Matrix.of H₂_kergen)) dist)
  · simp_all only
  apply dist_index_le_sound_contrapositive
  · assumption
  · simp_all only [not_le, gt_iff_lt]

theorem sat_translation_correct
  {n k₁ k₂ : ℕ} [NeZero n] [NeZero k₁] [NeZero k₂] [NeZero (n - k₁)] [NeZero (n - k₂)]
  (css : CSS_pair n k₁ k₂)
  (xkergen : Fin (n - k₁) → Fin n → ZMod 2)
  (xkergen_correct : kergen_correct css.H₁ xkergen)
  (zkergen : Fin (n - k₂) → Fin n → ZMod 2)
  (zkergen_correct : kergen_correct css.H₂ zkergen)
  (dist : Fin n) --why is this Fin?
   :
  let _ : NeZero (k₁ + k₂) := by
    rcases css with ⟨_, _, _, _, _, _, _, gt0_k₁⟩
    constructor; smt [gt0_k₁]
  dist_index_le n k₁ (n - k₂) (forget css.H₁) (forget (Matrix.of zkergen)) dist →
  dist_index_le n k₂ (n - k₁) (forget css.H₂) (forget (Matrix.of xkergen)) dist →
  dist ≤ css.toBSM.distance (by apply NeZero.pos) := by
  simp only
  intros h₁ h₂
  rw [CSS.toBSM_dist_eq]
  rcases css with ⟨C₁, C₂, _, H₁, H₂⟩
  simp only [CSS_pair.dX, CSS_pair.dZ
    ] at xkergen_correct zkergen_correct h₁ h₂ ⊢
  apply le_min
  · apply dist_index_le_sound
    · exact xkergen_correct
    · assumption
  · apply dist_index_le_sound
    · exact zkergen_correct
    · assumption
