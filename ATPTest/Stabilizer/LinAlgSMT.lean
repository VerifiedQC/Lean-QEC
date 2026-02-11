import Smt
import Mathlib.LinearAlgebra.Matrix.Defs
import Mathlib.Data.Finset.Range
import Mathlib.Data.Finset.Fold
import Mathlib.Algebra.Group.Embedding
import Mathlib.Tactic.Linarith.Frontend
import Mathlib.Data.ZMod.Defs

variable (e : ℕ → Bool)

--indexing function: ℕ → ℕ
def is_index_bool (I : ℕ → ℕ) (d n : ℕ) : Bool :=
  ((Finset.range d).fold and true (fun i => (I i) < n)) && (Finset.range (d-1)).fold and true (fun i => (I i < I (i + 1)))



def indexed_by (I : ℕ → ℕ) (d : ℕ) : ℕ → Bool := --
  fun i => (Finset.range d).fold or false (fun k => i = (I k))

instance : Std.Commutative Bool.xor := by
  constructor
  simp

def vec_inner_product (n : ℕ) (v₁ v₂ : ℕ → Bool) : Bool :=
  (Finset.range n).fold xor false (fun i => and (v₁ i) (v₂ i))

def mem_ker_bool (r : ℕ) (n : ℕ) (H : Matrix ℕ ℕ Bool) (x : ℕ → Bool) : Bool :=
  (Finset.range r).fold and true (fun k => ¬(vec_inner_product n x (H k)))

def not_mem_rowspace (ker_size n : ℕ) (H_ker : Matrix ℕ ℕ Bool) (x : ℕ → Bool) : Bool :=
  (Finset.range ker_size).fold or false (fun k => vec_inner_product n x (H_ker k))

--wait, this is already covered by is_index_bool. taking out of dist_index_le for now
def nontrivial_bool (n : ℕ) (x : ℕ → Bool) : Bool :=
  (Finset.range n).fold or false x

def dist_index_le (n r₁ z_ker_size : ℕ) (Hₓ H_z_ker : Matrix ℕ ℕ Bool) (d : ℕ) : Prop :=
  ∀ (I : ℕ → ℕ), let x := indexed_by I (d-1);
  !((is_index_bool I (d-1) n)
    && (mem_ker_bool r₁ n Hₓ x) && (not_mem_rowspace z_ker_size n H_z_ker x))

lemma Finset.fold_range_add_one {β : Type*}
  {op : β → β → β} [hc : Std.Commutative op] [ha : Std.Associative op] {n : ℕ} {f : ℕ → β} {b : β}
  : (Finset.range (n+1)).fold op b f = op (f n) ((Finset.range n).fold op b f) := sorry

variable {a b : ℕ}

instance h : IsLeftCancelAdd ℕ := sorry

#check (Finset.range b).map (addLeftEmbedding a)

def Finset.range_btw (a b : ℕ) : Finset ℕ := (Finset.range b) \  (Finset.range a)

@[simp]
lemma Finset.range_btw_zero (b : ℕ) : Finset.range_btw 0 b = Finset.range b := by
  unfold Finset.range_btw
  ext x
  simp

@[simp]
lemma Finset.range_btw_empty (a : ℕ) : Finset.range_btw a a = ∅ := by simp [range_btw]

@[simp]
lemma Finset.range_btw_one (a : ℕ) : Finset.range_btw a (a+1) = {a} := by
  unfold Finset.range_btw
  ext x
  simp only [mem_sdiff, mem_range, not_lt, mem_singleton]
  rw [le_antisymm_iff, Nat.lt_succ_iff]

lemma Finset.range_btw_split (m n₁ n₂ : ℕ)  :
  Finset.range_btw m (m + n₁ + n₂) =
  (Finset.range_btw m (m + n₁)) ∪ (Finset.range_btw (m + n₁) (m + n₁ + n₂)) := by
  ext x
  simp only [range_btw, mem_sdiff, mem_range, not_lt, mem_union]
  constructor
  · intro h₁
    by_cases h : x < m + n₁
    · exact Or.inl ⟨h, h₁.2⟩
    push_neg at h
    exact Or.inr ⟨h₁.1, h⟩
  rintro (⟨h₁, h₂⟩ | ⟨h₁, h₂⟩)
  · refine ⟨?_, h₂⟩
    apply lt_of_lt_of_le h₁ (by aesop)
  refine ⟨h₁, ?_⟩
  apply le_trans (by aesop) h₂

lemma Finset.range_btw_disj {m₁ n₁ m₂ n₂ : ℕ} (hle : n₁ ≤ m₂) :
  Disjoint (Finset.range_btw m₁ n₁) (Finset.range_btw m₂ n₂) := by
  rw [Finset.disjoint_iff_ne]
  simp [range_btw]
  intro a ha₁ h₂ b hb₁ hb₂ rfl
  have:= (lt_of_lt_of_le ha₁ (hle.trans hb₂))
  simp at this

lemma Finset.fold_range_split_idem {β : Type*}
  {op : β → β → β} [hc : Std.Commutative op] [ha : Std.Associative op] {b : β} [hi : Std.LawfulCommIdentity op b] {n : ℕ} {f : ℕ → β}
  : (Finset.range (2 * n)).fold op b f = op ((Finset.range_btw 0 n).fold op b f) ((Finset.range_btw n (2*n)).fold op b f):= by
  rw [←Finset.range_btw_zero, Nat.two_mul, ←(@zero_add _ _ (n + n)), ←add_assoc, Finset.range_btw_split]
  rw [←Finset.disjUnion_eq_union _ _ (Finset.range_btw_disj le_rfl)]
  convert (Finset.fold_disjUnion _)
  · rw [hi.left_id]
  · rw [zero_add]
  rw [zero_add]

lemma Finset.fold_range_split' {β : Type*}
  {op : β → β → β} [hc : Std.Commutative op] [ha : Std.Associative op] {b : β} [hi : Std.LawfulCommIdentity op b] {n : ℕ} {f : ℕ → β}
  : (Finset.range (2 * n + 3)).fold op b f = op ((Finset.range_btw 0 (n+2)).fold op b f) ((Finset.range_btw (n+2) (2*n + 3)).fold op b f):= sorry


def Matrix.castnat {a b : ℕ} {α : Type*} [Zero α] (M : Matrix (Fin a) (Fin b) α) : Matrix ℕ ℕ α
  := fun i j => if h₁: i < a then (if h₂: j < b then M ⟨i, h₁⟩ ⟨j, h₂⟩ else 0) else 0

def Matrix.castbool {α β : Type*} (M : Matrix α β (ZMod 2)) := fun i j => Bool.ofNat (M i j).val



open Lean Meta Elab Tactic Syntax
elab "unfold_range"
 : tactic => do
  evalTactic (← `(tactic| repeat rw [Finset.fold_range_add_one]))
  evalTactic (← `(tactic| repeat rw [Finset.range_zero]))
  evalTactic (← `(tactic| repeat rw [Finset.fold_empty]))

--before calling:
set_option maxHeartbeats 0
elab "prep_smt"
 : tactic => do
  evalTactic (← `(tactic| dsimp))
  evalTactic (← `(tactic| unfold is_index_bool))
  evalTactic (← `(tactic| unfold_range))
  evalTactic (← `(tactic| rw [Bool.and_true]))
  evalTactic (← `(tactic| unfold nontrivial_bool))
  evalTactic (← `(tactic| unfold_range))
  evalTactic (← `(tactic| rw [Bool.or_false]))
  evalTactic (← `(tactic| unfold mem_ker_bool))
  evalTactic (← `(tactic| unfold_range))
  evalTactic (← `(tactic| rw [Bool.and_true]))
  evalTactic (← `(tactic| unfold vec_inner_product))
  evalTactic (← `(tactic| unfold_range))
  evalTactic (← `(tactic| rw [Bool.xor_false]))
  evalTactic (← `(tactic| unfold not_mem_rowspace))
  evalTactic (← `(tactic| unfold_range))
  evalTactic (← `(tactic| unfold vec_inner_product))
  evalTactic (← `(tactic| unfold_range))
  evalTactic (← `(tactic| rw [Bool.xor_false]))
  evalTactic (← `(tactic| unfold indexed_by))
  evalTactic (← `(tactic| unfold_range))
