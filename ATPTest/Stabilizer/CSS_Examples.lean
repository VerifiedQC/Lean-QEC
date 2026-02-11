import ATPTest.Stabilizer.CSS
import ATPTest.Stabilizer.LinAlg
import ATPTest.Stabilizer.LinAlgSMT

def q9_X := Matrix.castnat (Matrix.castbool !![1, 1, 1, 1, 1, 1, 0, 0, 0 ;
              0, 0, 0, 1, 1, 1, 1, 1, 1
])

def q9_Z := Matrix.castnat (Matrix.castbool !![
  1, 1, 0, 0, 0, 0, 0, 0, 0;
  0, 1, 1, 0, 0, 0, 0, 0, 0;
  0, 0, 0, 1, 1, 0, 0, 0, 0;
  0, 0, 0, 0, 1, 1, 0, 0, 0;
  0, 0, 0, 0, 0, 0, 1, 1, 0;
  0, 0, 0, 0, 0, 0, 0, 1, 1;
])

def q9x_ker := Matrix.castnat (Matrix.castbool !![1,1,0,0,0,0,0,0,0;
1,0,1,0,0,0,0,0,0;
0,0,0,1,1,0,0,0,0;
0,0,0,1,0,1,0,0,0;
1,0,0,1,0,0,1,0,0;
1,0,0,1,0,0,0,1,0;
1,0,0,1,0,0,0,0,1;
])

def q9z_ker := Matrix.castnat (Matrix.castbool !![1,1,1,0,0,0,0,0,0;
0,0,0,1,1,1,0,0,0;
0,0,0,0,0,0,1,1,1;
])

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
  --smt [h, h2]
  sorry




theorem dist9z_3 : dist_index_le 9 2 3 q9_X q9z_ker 3 := by
  intro I
  dsimp
  simp [is_index_bool,
    indexed_by, Finset.fold_range_add_one, mem_ker_bool, vec_inner_product, q9_X,
    Matrix.castnat, Matrix.castbool, ZMod.val, q9z_ker, not_mem_rowspace]
  simp_rw [@Eq.comm _ _ (I _)]
  smt

theorem dist9x_3 : dist_index_le 9 6 2 q9_Z q9x_ker 3 := by
  intro I
  dsimp
  simp [is_index_bool,
    indexed_by, Finset.fold_range_add_one, mem_ker_bool, vec_inner_product, q9_Z,
    Matrix.castnat, Matrix.castbool, ZMod.val, q9x_ker, not_mem_rowspace]
  simp_rw [@Eq.comm _ _ (I _)]
  smt
