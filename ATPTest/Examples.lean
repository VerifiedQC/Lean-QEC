import ATPTest.Stabilizer


open Qubit

def three_qubit_encode : QCode 1 3 := fun (ψ : Ket Qubit) =>
  (((ψ ⊗ qub_zero) ⊗ qub_zero).uapply
    (Matrix.unitary_kron C[X] (1 : 𝐔[Qubit]))).uapply
      (unitary_fin_equiv (Equiv.prodAssoc _ _ _).symm (C[Matrix.unitary_kron (1 : 𝐔[Qubit]) X]))

   /-
   ((unitary_fin_equiv (Equiv.prodAssoc _ _ _)
   (Matrix.unitary_kron C[X] (1 : 𝐔[Qubit])))).uapply --CX(2, 3)
   C[Matrix.unitary_kron (1 : 𝐔[Qubit]) X] --CX(1, 3)
-/
lemma three_qubit_encode_correct (ψ : Ket Qubit) : three_qubit_encode ψ =
  (qub_zero ⊗ (qub_zero ⊗ qub_zero)).sum
  (qub_one ⊗ (qub_one ⊗ qub_one)) (ψ.vec 0) (ψ.vec 1) (single_qub_normalized _) (prod_orth zero_one_orth (prod_orth zero_one_orth zero_one_orth))
  := sorry

theorem three_qub_detects_one_x : three_qubit_encode.detects_P_error_of_weight
