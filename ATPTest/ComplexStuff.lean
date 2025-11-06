import Mathlib.Data.Complex.Basic
import Mathlib.Algebra.Group.Subgroup.Defs
import Mathlib.Data.Fintype.Basic
import Mathlib.Algebra.Group.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Algebra.Group.Units.Defs
import ATPTest.Unitary.Basic
import ATPTest.Unitary.Pauli

-- some Aristotle proofs break without this
set_option maxHeartbeats 0

noncomputable section

-- undergrad-level subgroup test
-- somehow can't manage to find this in the mathlib

def subgroup_test {G} [Group G] (N : Set G) :=
  (Nonempty N) ∧ (forall (a b : G), a ∈ N → b ∈ N → a * b⁻¹ ∈ N)

-- aristotle
lemma mul_mem_by_test {G} [Group G] {N : Set G} (test: subgroup_test N) (x y : G) :
  x ∈ N → y ∈ N → x * y ∈ N := by
  -- By the subgroup_test, we know that for any a and b in N, a * b⁻¹ is in N. Let's take a = x and b = y⁻¹.
  have h_inv : x ∈ N → y ∈ N → x * (y⁻¹)⁻¹ ∈ N := by
    -- By the subgroup_test, we know that for any a and b in N, a * b⁻¹ is in N. Let's take a = x and b = y⁻¹. Since y is in N, y⁻¹ is also in N (because N is a subgroup, so it's closed under inverses). Therefore, x * (y⁻¹)⁻¹ = x * y is in N.
    intros hx hy; exact test.2 x (y⁻¹) hx (by
    -- By the subgroup_test, we know that for any a and b in N, a * b⁻¹ is in N. Let's take a = 1 and b = y. Since 1 is in N (because N is a subgroup and contains the identity), and y is in N, then 1 * y⁻¹ = y⁻¹ is in N.
    have h_inv : 1 ∈ N ∧ y ∈ N → y⁻¹ ∈ N := by
      rintro ⟨ h1, hy ⟩ ; simpa using test.2 _ _ h1 hy;
    exact h_inv ⟨ by simpa using test.2 _ _ hx hx, hy ⟩);
  aesop

-- aristotle
lemma one_mem_by_test {G} [Group G] {N : Set G} (test: subgroup_test N) : 1 ∈ N := by
  -- Since N is nonempty, there exists some element a in N. Then, by the subgroup test, a * a⁻¹ should be in N. But a * a⁻¹ is the identity element, so 1 is in N.
  obtain ⟨a, ha⟩ : ∃ a, a ∈ N := by
    -- Since $N$ is nonempty, we can obtain an element $a \in N$.
    apply test.left.elim;
    -- Since $a \in N$, we can use $a$ itself as the witness.
    intro a
    use a.val;
    -- Since $a$ is an element of the set $N$, by definition of the set, $a$ must be in $N$.
    apply a.property
  have h1 : a * a⁻¹ ∈ N := by
    -- Apply the subgroup test with x = a and y = a.
    apply test.right a a ha ha
  simp at h1
  exact h1

-- aristotle
lemma inv_mem_by_test {G} [Group G] {N : Set G} (test: subgroup_test N) (x : G) :
  x ∈ N → x⁻¹ ∈ N := by
  -- By the subgroup test, since $x \in N$, we have $1 \in N$.
  have h_one : 1 ∈ N := by
    -- By the subgroup test, since $x \in N$, we have $x * x⁻¹ \in N$, which simplifies to $1 \in N$.
    apply one_mem_by_test; assumption;
  -- By the subgroup test, since $1 \in N$ and $x \in N$, we have $1 * x⁻¹ = x⁻¹ \in N$.
  intro hx
  have := test.right 1 x h_one hx
  simp at this
  exact this

def subgroup_by_test {G} [Group G] {N : Set G} (test: subgroup_test N) : Subgroup G where
  carrier := N
  mul_mem' := by apply mul_mem_by_test; trivial
  one_mem' := by apply one_mem_by_test; trivial
  inv_mem' := by apply inv_mem_by_test; trivial

-- Now, the actually useful part

-- aristotle
lemma IsUnitI : IsUnit Complex.I := by
  simp +zetaDelta at *

def iu := IsUnitI.unit
def μ₄ : Set ℂˣ := {1, -1, iu, -iu}

-- aristotle
lemma sg_test_μ₄ : subgroup_test μ₄ := by
  -- Let's verify that μ₄ is nonempty and closed under multiplication and inverses.
  have h_nonempty : Nonempty μ₄ := by
    -- Since 1 is in μ₄, we can conclude that μ₄ is nonempty.
    use 1
    simp [μ₄]
  have h_closed : ∀ a b : ℂˣ, a ∈ μ₄ → b ∈ μ₄ → a * b⁻¹ ∈ μ₄ := by
    -- Let's verify that μ₄ is closed under multiplication and inverses by checking all possible pairs.
    intros a b ha hb
    simp [μ₄] at ha hb ⊢
    aesop
    all_goals generalize_proofs at *;
    · -- Since $iu$ is the unit $i$, its inverse is $-i$.
      have h_inv : iu⁻¹ = -iu := by
        -- Since $iu = i$, we have $iu⁻¹ = -i$. Therefore, $-iu⁻¹ = -(-i) = i = iu$ by definition of $iu$.
        have h_inv : iu⁻¹ = -iu := by
          have h_iu : iu = Units.mk0 Complex.I (by
          exact Complex.I_ne_zero) := by
            exact?
          rw [h_iu]
          exact Units.ext <| by simp +decide [ Complex.ext_iff ] ;
        generalize_proofs at *;
        -- Apply the hypothesis `h_inv` directly to conclude the proof.
        rw [h_inv]
      aesop;
    · -- Since $iu = i$, we have $iu⁻¹ = -i$. Therefore, $-iu⁻¹ = -(-i) = i = iu$.
      have h_inv : iu⁻¹ = -iu := by
        -- Since $iu = i$, we have $iu⁻¹ = -i$. Therefore, $-iu⁻¹ = -(-i) = i = iu$ by definition of $iu$.
        have h_inv : iu⁻¹ = -iu := by
          have h_iu : iu = Units.mk0 Complex.I (by
          exact Complex.I_ne_zero) := by
            exact?
          rw [h_iu]
          exact Units.ext <| by simp +decide [ Complex.ext_iff ] ;
        generalize_proofs at *;
        -- Apply the hypothesis `h_inv` directly to conclude the proof.
        rw [h_inv]
      rw [h_inv]
      simp [iu];
    · -- Since $iu$ is the unit corresponding to $i$, we have $iu⁻¹ = -i$.
      have h_inv : iu⁻¹ = -iu := by
        -- Since $iu = i$, we have $iu⁻¹ = -i$. Therefore, $-iu⁻¹ = -(-i) = i = iu$ by definition of $iu$.
        have h_inv : iu⁻¹ = -iu := by
          have h_iu : iu = Units.mk0 Complex.I (by
          exact Complex.I_ne_zero) := by
            exact?
          rw [h_iu]
          exact Units.ext <| by simp +decide [ Complex.ext_iff ] ;
        generalize_proofs at *;
        -- Apply the hypothesis `h_inv` directly to conclude the proof.
        rw [h_inv]
      all_goals generalize_proofs at *; aesop;
    · simp +decide [ iu ];
      -- Since $i$ is a unit, its inverse is $-i$.
      right; right; right; exact (by
      -- Since $i$ is a unit, its inverse is $-i$, so we can conclude that $IsUnitI.unit⁻¹ = -IsUnitI.unit$.
      ext; simp [IsUnitI])
      all_goals generalize_proofs at *;
  exact ⟨h_nonempty, h_closed⟩
  all_goals generalize_proofs at *

instance μ₄_grp : Group μ₄ := (subgroup_by_test sg_test_μ₄).toGroup

-- Now, if we must use this funny `phase` bundle...

def pgphase_i : pgroup_phases := ⟨⟨Complex.I, by norm_num⟩, by simp [pgroup_phases]⟩
def pgphase_ni : pgroup_phases := ⟨⟨-Complex.I, by norm_num⟩, by simp [pgroup_phases]⟩

def μ₄_1 : μ₄ := ⟨1, by rw [μ₄]; simp⟩
def μ₄_n1 : μ₄ := ⟨-1, by rw [μ₄]; simp⟩
def μ₄_i : μ₄ := ⟨iu, by rw [μ₄]; simp⟩
def μ₄_ni : μ₄ := ⟨-iu, by rw [μ₄]; simp⟩

def addPhase_toFun (ζ : μ₄) : pgroup_phases :=
  if ζ = μ₄_1 then pgphase_1
  else if ζ = μ₄_n1 then pgphase_n1
  else if ζ = μ₄_i then pgphase_i
  else pgphase_ni

def addPhase_invFun (p : pgroup_phases) : μ₄ :=
  let v := p.1.1
  if v = 1 then μ₄_1
  else if v = -1 then μ₄_n1
  else if v = Complex.I then μ₄_i
  else μ₄_ni

-- aristotle
lemma addPhase_leftInv x : addPhase_invFun (addPhase_toFun x) = x := by
  -- By definition of addPhase_toFun and addPhase_invFun, we can check each case to show that they are inverses.
  have h_cases : ∀ x : μ₄, addPhase_invFun (addPhase_toFun x) = x := by
    norm_num +zetaDelta at *;
    -- By definition of addPhase_toFun and addPhase_invFun, we can check each case to show that they are inverses. We'll do this by considering each element of μ₄.
    intro a ha
    cases' ha with ha ha
    aesop
    all_goals generalize_proofs at *;
    · -- By definition of addPhase_toFun and addPhase_invFun, we can check each case to show that they are inverses. We'll do this by considering each element of μ₄ and showing that the inverse function returns it.
      simp [addPhase_toFun, addPhase_invFun];
      -- By definition of addPhase_toFun and addPhase_invFun, we can check each case to show that they are inverses. We'll do this by considering each element of μ₄ and showing that the inverse function returns it. In this case, the element is 1, so the inverse function should return 1.
      simp [μ₄_1, μ₄_n1, μ₄_i, μ₄_ni] at *;
      exact fun h => False.elim <| h <| by exact rfl;
    · unfold addPhase_invFun addPhase_toFun; aesop;
      all_goals norm_num [ Complex.ext_iff, pgphase_1, pgphase_n1, pgphase_i, pgphase_ni ] at * <;> tauto;
  exact h_cases x

-- aristotle
lemma addPhase_rightInv x : addPhase_toFun (addPhase_invFun x) = x := by
  -- By definition of addPhase_toFun and addPhase_invFun, we can show that they are inverses of each other.
  have h_inv : ∀ x : pgroup_phases, addPhase_toFun (addPhase_invFun x) = x := by
    -- By definition of addPhase_invFun and addPhase_toFun, we can show that they are inverses of each other.
    intros x
    simp [addPhase_invFun, addPhase_toFun];
    rcases x with ⟨ ⟨ z, hz ⟩, hx ⟩ ; aesop;
    all_goals simp_all +decide [ Finset.ext_iff, Set.ext_iff, pgphase_1, pgphase_n1, pgphase_i, pgphase_ni ] ;
    all_goals simp_all +decide [ Complex.ext_iff, μ₄_1, μ₄_n1, μ₄_i, μ₄_ni ] ;
    · -- Since $iu$ is the imaginary unit, it is not equal to $1$.
      have h_iu_ne_one : iu ≠ 1 := by
        -- Since $iu$ is the unit corresponding to $Complex.I$, and $Complex.I \neq 1$, we have $iu \neq 1$.
        simp [iu] at *;
        exact ne_of_apply_ne ( fun x => x.val ) ( by norm_num [ Complex.ext_iff ] )
      all_goals simp_all +decide [ iu ] ;
    · -- Since $iu = -1$, we have a contradiction because $iu$ is the unit of $Complex.I$, which is $i$, and $i \neq -1$.
      have h_contra : iu = Complex.I := by
        exact?;
      norm_num [ h_1, Complex.ext_iff ] at h_contra;
    · -- Since $-iu = 1$ is false, the implication $h_2$ must be false, leading to a contradiction.
      have h_contra : ¬(-iu = 1) := by
        -- Since $iu = Complex.I$, we have $-iu = -Complex.I$.
        simp [iu];
        exact ne_of_apply_ne ( fun x => x.val ) ( by norm_num [ Complex.ext_iff ] );
      aesop;
    · injection h_2 with h_2 ; aesop;
      · norm_num [ Complex.ext_iff ] at h_2;
      · norm_num [ Complex.ext_iff ] at h_2;
    · unfold pgroup_phases at hx; aesop;
  exact h_inv _

def addPhase [Group μ₄] : μ₄ ≃ pgroup_phases where
  toFun := addPhase_toFun
  invFun := addPhase_invFun
  left_inv := by apply addPhase_leftInv
  right_inv := by apply addPhase_rightInv

def phases_mul [Group μ₄] (x y : pgroup_phases) :=
  addPhase ((addPhase.symm x) * (addPhase.symm y))

def inv_ph (x : pgroup_phases) := addPhase ((addPhase.symm x)⁻¹)
local instance : Mul pgroup_phases where mul := phases_mul
local instance : Inv pgroup_phases where inv := inv_ph
local instance : One pgroup_phases where one := addPhase 1

-- aristotle
lemma phases_grp_mul_assoc (x y z : pgroup_phases) :
  x * y * z = x * (y * z) := by
  aesop
  generalize_proofs at *;
  -- Since addPhase is a group isomorphism, the associativity in μ₄ implies associativity in pgroup_phases.
  have h_assoc : ∀ (x y z : μ₄), (x * y) * z = x * (y * z) := by
    aesop
    all_goals generalize_proofs at *;
    exact mul_assoc _ _ _
  generalize_proofs at *;
  -- Since addPhase is a group isomorphism, the multiplication in pgroup_phases is the same as the multiplication in μ₄ when restricted to pgroup_phases.
  have h_mul_eq : ∀ x y : pgroup_phases, phases_mul x y = addPhase ((addPhase.symm x) * (addPhase.symm y)) := by
    exact?
  generalize_proofs at *;
  -- Since addPhase is a group isomorphism, the multiplication in pgroup_phases is defined in terms of the multiplication in μ₄. Therefore, the associativity in μ₄ implies associativity in pgroup_phases.
  have h_assoc_pgroup : ∀ x y z : pgroup_phases, phases_mul (phases_mul x y) z = phases_mul x (phases_mul y z) := by
    aesop
    all_goals generalize_proofs at *;
  all_goals generalize_proofs at *;
  exact h_assoc_pgroup ⟨val, property⟩ ⟨val_1, property_1⟩ ⟨val_2, property_2⟩
  all_goals generalize_proofs at *;

-- aristotle
lemma phases_grp_one_mul (a : pgroup_phases) : 1 * a = a := by
  -- By definition of multiplication in the group, we have that multiplying by the identity element leaves the element unchanged.
  have h_id_mul : ∀ (g : μ₄), addPhase (1 * g) = addPhase g := by
    -- Since 1 is the identity element in the group, multiplying by 1 doesn't change the element.
    simp [mul_one]
  generalize_proofs at *;
  norm_num +zetaDelta at *;
  -- Since addPhase is an equivalence, applying it to the identity element gives the identity element.
  have h_id : addPhase 1 = ⟨⟨1, by
    norm_num [ Norm.norm ]⟩, by
    exact Finset.mem_insert_self _ _⟩ := by
    -- By definition of addPhase, we know that addPhase 1 is the element in pgroup_phases corresponding to 1.
    simp [addPhase];
    unfold addPhase_toFun; aesop;
    · exact?;
    · exact?;
    · contrapose! h; aesop;
  generalize_proofs at *;
  convert h_id_mul using 1
  all_goals generalize_proofs at *;
  -- Since addPhase is an equivalence, applying it to the identity element gives the identity element. Therefore, phases_mul (addPhase 1) y is equal to y.
  have h_id_mul : ∀ (y : pgroup_phases), phases_mul (addPhase 1) y = y := by
    -- Since addPhase is an equivalence, applying it to the identity element gives the identity element. Therefore, phases_mul (addPhase 1) y is equal to y by definition of phases_mul.
    intros y
    simp [phases_mul, h_id];
    simp +decide [ ← h_id ]
  generalize_proofs at *;
  exact iff_of_true ( h_id_mul _ ) trivial

-- aristotle
lemma phases_grp_left_inv (a : pgroup_phases) :
  a⁻¹ * a = 1 := by
  -- Since `addPhase` is a bijection, its inverse function `addPhase_invFun` is also a bijection.
  have h_addPhase_bij : Function.Bijective addPhase := by
    exact?
  generalize_proofs at *;
  cases h_addPhase_bij ; aesop
  all_goals generalize_proofs at *;
  -- Since `addPhase` is a bijection, we can rewrite the multiplication in terms of the group operation on `μ₄`.
  have h_mul : phases_mul (addPhase ((addPhase.symm ⟨val, property⟩)⁻¹)) ⟨val, property⟩ = addPhase ((addPhase.symm ⟨val, property⟩)⁻¹ * addPhase.symm ⟨val, property⟩) := by
    unfold phases_mul; aesop;
  generalize_proofs at *;
  aesop
  all_goals generalize_proofs at *

def phases_grp' [Group μ₄] : Group pgroup_phases := Group.ofLeftAxioms
  phases_grp_mul_assoc phases_grp_one_mul phases_grp_left_inv
