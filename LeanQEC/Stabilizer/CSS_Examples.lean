import LeanQEC.Stabilizer.CSS
import LeanQEC.Stabilizer.LinAlg
import LeanQEC.Stabilizer.LinAlgSMT

def Shor_X : Matrix (Fin 2) (Fin 9) (ZMod 2) :=  !![1, 1, 1, 1, 1, 1, 0, 0, 0 ;
              0, 0, 0, 1, 1, 1, 1, 1, 1
]


def Shor_Z : Matrix (Fin 6) (Fin 9) (ZMod 2) :=  !![
  1, 1, 0, 0, 0, 0, 0, 0, 0;
  0, 1, 1, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 1, 0, 0, 0, 0;
  0, 0, 0, 0, 1, 1, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 1, 1, 0;
  0, 0, 0, 0, 0, 0, 0, 1, 1;
]

lemma Shor_Z_ind : LinearIndependent (ZMod 2) Shor_Z.row := sorry

lemma Shor_X_ind : LinearIndependent (ZMod 2) Shor_X.row := sorry


def Shor_Z_cast := Matrix.castnat (Matrix.castbool Shor_Z)

def Shor_X_cast := Matrix.castnat (Matrix.castbool Shor_X)


def Shor_X_codespace := Shor_X.toCodeSpace

def Shor_Z_codespace := Shor_Z.toCodeSpace



lemma Shor_orth : Shor_Z.mutually_orth_rows Shor_X := sorry



def Shor_X_ker := Matrix.castnat (Matrix.castbool !![1,1,0,0,0,0,0,0,0;
1,0,1,0,0,0,0,0,0;
0,0,0,1,1,0,0,0,0;
0,0,0,1,0,1,0,0,0;
1,0,0,1,0,0,1,0,0;
1,0,0,1,0,0,0,1,0;
1,0,0,1,0,0,0,0,1;
])

def Shor_Z_ker := Matrix.castnat (Matrix.castbool !![1,1,1,0,0,0,0,0,0;
0,0,0,1,1,1,0,0,0;
0,0,0,0,0,0,1,1,1;
])

def Shor_pair : CSS_pair 9 6 2 := CSS_pair.of_matrices Shor_Z Shor_X Shor_orth Shor_Z_ind Shor_X_ind



example (x : ℕ) (h : (x < 9)) (h2 : (8 = x ∨ 7 = x ∨ 6 = x ∨ 5 = x ∨ 4 = x ∨ 3 = x ∨ 2 = x ∨ 1 = x ∨ 0 = x)):
 ((Bool.xor (x = 0) (Bool.xor (x = 1) (Bool.xor (x = 2) (Bool.xor (x = 3) (Bool.xor (x = 4) (x = 5)))))) ||
  (Bool.xor (x = 3) (Bool.xor (x = 4) (Bool.xor (x = 5) (Bool.xor (x = 6) (Bool.xor (x = 7) (x = 8)))))))
  := by
  smt [h, h2]

--observe two identical examples, but proof construction fails in the second because the equalities are stated (num = x) instead of (x = num)
--no clue why this is the issue
example {x : ℕ} (h : (x < 9)) (h2 : (8 = x ∨ 7 = x ∨ 6 = x ∨ 5 = x ∨ 4 = x ∨ 3 = x ∨ 2 = x ∨ 1 = x ∨ 0 = x)) :
    (
            (Bool.xor (8 = x) (Bool.xor (7 = x) (Bool.xor (6 = x) (Bool.xor (5 = x) (Bool.xor (4 = x) (3 = x)))))) ||
            (Bool.xor (4 = x) (Bool.xor (3 = x) (Bool.xor (2 = x) (Bool.xor (1 = x)  (0 = x)))))) =
  true := by
  simp_rw [eq_comm] at h2 ⊢
  smt [h, h2]




theorem dist9z_3 : dist_index_le 9 2 3 Shor_X_cast Shor_Z_ker 3 := by
  intro I
  dsimp
  simp [is_index_bool,
    indexed_by, Finset.fold_range_add_one, mem_ker_bool, vec_inner_product, Shor_X_cast, Shor_X,
    Matrix.castnat, Matrix.castbool, Shor_Z_ker, not_mem_rowspace]
  simp_rw [@Eq.comm _ _ (I _)]
  smt

theorem dist9x_3 : dist_index_le 9 6 2 Shor_Z_cast Shor_X_ker 3 := by
  intro I
  dsimp
  simp [is_index_bool,
    indexed_by, Finset.fold_range_add_one, mem_ker_bool, vec_inner_product, Shor_Z_cast, Shor_Z,
    Matrix.castnat, Matrix.castbool, Shor_X_ker, not_mem_rowspace]
  simp_rw [@Eq.comm _ _ (I _)]
  smt

def Steane_mat := Matrix.castnat (Matrix.castbool !![
  1, 0, 0, 1, 0, 1, 1;
  0, 1, 0, 1, 1, 0, 1;
  0, 0, 1, 0, 1, 1, 1;
])

def Steane_ker := Matrix.castnat (Matrix.castbool !![
  1,1,0,1,0,0,0;
  0,1,1,0,1,0,0;
  1,0,1,0,0,1,0;
  1,1,1,0,0,0,1;
])

theorem dist_steane_3 : dist_index_le 7 3 4 Steane_mat Steane_ker 3 := by
  intro I
  dsimp
  simp [is_index_bool,
    indexed_by, Finset.fold_range_add_one, mem_ker_bool, vec_inner_product, Steane_ker,
    Matrix.castnat, Matrix.castbool, ZMod.val, Steane_mat, not_mem_rowspace]
  simp_rw [@Eq.comm _ _ (I _)]
  smt

def Golay_mat := Matrix.castnat (Matrix.castbool !![
0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1;
1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0;
0, 1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0;
1, 1, 0, 1, 1, 1, 0, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0;
1, 1, 1, 1, 0, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0;
1, 0, 1, 0, 1, 0, 1, 1, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0;
0, 0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0;
0, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0;
0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0;
1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0;
1, 0, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0;

])

def Golay_ker := Matrix.castnat (Matrix.castbool !![
  1,1,0,0,0,1,1,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0;
0,1,1,0,0,0,1,1,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0;
1,1,1,1,0,1,1,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0,0;
0,1,1,1,1,0,1,1,0,1,0,0,0,0,1,0,0,0,0,0,0,0,0;
0,0,1,1,1,1,0,1,1,0,1,0,0,0,0,1,0,0,0,0,0,0,0;
1,1,0,1,1,0,0,1,1,0,0,0,0,0,0,0,1,0,0,0,0,0,0;
0,1,1,0,1,1,0,0,1,1,0,0,0,0,0,0,0,1,0,0,0,0,0;
0,0,1,1,0,1,1,0,0,1,1,0,0,0,0,0,0,0,1,0,0,0,0;
1,1,0,1,1,1,0,0,0,1,1,0,0,0,0,0,0,0,0,1,0,0,0;
1,0,1,0,1,0,0,1,0,1,1,0,0,0,0,0,0,0,0,0,1,0,0;
1,0,0,1,0,0,1,1,1,1,1,0,0,0,0,0,0,0,0,0,0,1,0;
1,0,0,0,1,1,1,0,1,0,1,0,0,0,0,0,0,0,0,0,0,0,1;
])
/-
set_option maxHeartbeats 0
theorem dist_golay_7 : dist_index_le 23 11 12 Golay_mat Golay_ker 7 := by
  intro I
  dsimp
  simp [is_index_bool,
    indexed_by, Finset.fold_range_add_one, mem_ker_bool, vec_inner_product, Golay_ker,
    Matrix.castnat, Matrix.castbool, ZMod.val, Golay_mat, not_mem_rowspace]
  simp_rw [@Eq.comm _ _ (I _)]
  --smt
  --run smt on this at your own risk!!!!
  smt
-/
