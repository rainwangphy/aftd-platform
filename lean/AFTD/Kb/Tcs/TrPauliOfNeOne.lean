import AFTD.Prelude
import AFTD.Kb.Tcs.PauliMatrix
import AFTD.Kb.Tcs.PauliString
import AFTD.Kb.Tcs.PauliBasis
import AFTD.Kb.Tcs.PauliBasisToMatrix

/-!
# tr_pauli_of_ne_one

Topic: quantum   Node: 0b283a110b0b

Provenance: helper lemma. arXiv:2610.37807, Lemma 10 proof

If a Pauli string on $n$ qubits contains at least one non-identity single-qubit Pauli operator, then its tensor-product matrix has trace zero.
-/

/-- Any Pauli string having at least one non-identity single-qubit factor has trace zero. -/
lemma tr_pauli_of_ne_one (n : ℕ) (p : PauliString n)
    (hp : ∃ i : Fin n, p i ≠ PauliBasis.I) :
    (pauliMatrix p).trace = 0 := by
  obtain ⟨k, hk⟩ := hp
  have hkey : (pauliMatrix p).trace
      = ∑ i : Fin n → Fin 2, ∏ k, (p k).toMatrix (i k) (i k) := rfl
  have hfac : (∑ i : Fin n → Fin 2, ∏ k, (p k).toMatrix (i k) (i k))
      = ∏ k, ∑ a : Fin 2, (p k).toMatrix a a := by
    rw [← Finset.sum_prod_piFinset (s := Finset.univ)
          (g := fun k (a : Fin 2) => (p k).toMatrix a a)]
    congr 1
  rw [hkey, hfac]
  apply Finset.prod_eq_zero (Finset.mem_univ k)
  cases hpk : p k with
  | I => exact absurd hpk hk
  | X => simp [PauliBasis.toMatrix, sigmaX]
  | Y => simp [PauliBasis.toMatrix, sigmaY]
  | Z => simp [PauliBasis.toMatrix, sigmaZ]
