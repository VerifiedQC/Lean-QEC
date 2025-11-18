import Mathlib

noncomputable section

structure phase where
  z : ℂ
  z_norm : ‖z‖ = 1
deriving DecidableEq

instance : Coe phase ℂ where
  coe p := p.z

namespace Phase

def mul (p q : phase) : phase :=
  {
    z := p * q
    z_norm := by simp [p.z_norm, q.z_norm]
  }

instance : Mul phase where
  mul := mul

def phase_star (p : phase) : phase :=
  {
    z := star p
    z_norm := by simp [p.2]
  }


@[simp]
lemma phase_mul_eq {p q : phase} : p * q = ⟨p.1 * q.1, by simp [p.z_norm, q.z_norm]⟩ := by rfl

end Phase

@[simp]
def phase_id : phase :=
  {
    z := 1
    z_norm := by norm_num
  }
