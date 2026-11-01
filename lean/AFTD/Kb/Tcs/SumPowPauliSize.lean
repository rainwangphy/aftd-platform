import AFTD.Prelude
import AFTD.Kb.Tcs.PauliSize
import AFTD.Kb.Tcs.PauliLabel

/-!
# sum_pow_pauli_size

Topic: quantum   Node: 2e8ebab8cef9

Provenance: helper lemma. step towards op_757_all_to_all_cnot_lower_bound

Weight enumerator of Pauli labels: summed over all 4^k labels, x^(k - pauli_size p) equals (x+3)^k. Per qubit the four Pauli choices contribute x (identity), 1, 1, 1 (X, Y, Z).
-/

open Finset

def sum_pow_pauli_size_equiv (k : ℕ) : (Fin k → ZMod 2 × ZMod 2) ≃ PauliLabel k :=
  Equiv.arrowProdEquivProdArrow (Fin k) (fun _ => ZMod 2) (fun _ => ZMod 2)

lemma sum_pow_pauli_size_prod_per_qubit {k x : ℕ} (p : PauliLabel k) :
    x ^ (k - pauli_size p)
      = ∏ i : Fin k, (if p.1 i = 0 then (if p.2 i = 0 then x else 1) else 1) := by
  have hcard : k - pauli_size p = (univ.filter (fun i : Fin k => p.1 i = 0 ∧ p.2 i = 0)).card := by
    show k - (univ.filter (fun i : Fin k => p.1 i ≠ 0 ∨ p.2 i ≠ 0)).card = _
    have h2 := Finset.card_filter_add_card_filter_not (s := (univ : Finset (Fin k)))
      (p := fun i => p.1 i ≠ 0 ∨ p.2 i ≠ 0)
    have h3 : (univ.filter (fun i : Fin k => ¬ (p.1 i ≠ 0 ∨ p.2 i ≠ 0)))
        = univ.filter (fun i : Fin k => p.1 i = 0 ∧ p.2 i = 0) := by
      apply Finset.filter_congr
      intro i _
      simp
    rw [h3, card_univ, Fintype.card_fin] at h2
    omega
  rw [hcard]
  have hstep : (∏ i : Fin k, (if p.1 i = 0 then (if p.2 i = 0 then x else 1) else 1))
      = ∏ i : Fin k, (if (p.1 i = 0 ∧ p.2 i = 0) then x else 1) := by
    apply Finset.prod_congr rfl
    intro i _
    by_cases h1 : p.1 i = 0 <;> by_cases h2 : p.2 i = 0 <;> simp [h1, h2]
  rw [hstep]
  rw [← Finset.prod_filter (s := univ) (p := fun i : Fin k => p.1 i = 0 ∧ p.2 i = 0) (f := fun _ => x)]
  rw [Finset.prod_const]

lemma sum_pow_pauli_size_sum_zmod2_sq (x : ℕ) :
    (∑ c : ZMod 2 × ZMod 2, (if c.1 = 0 then (if c.2 = 0 then x else 1) else 1)) = x + 3 := by
  have hu : (univ : Finset (ZMod 2 × ZMod 2)) = {(0, 0), (0, 1), (1, 0), (1, 1)} := by decide
  rw [hu]
  simp

/-- Weight enumerator of Pauli labels: `∑ p, x^(k - pauli_size p) = (x+3)^k`. -/
theorem sum_pow_pauli_size (k x : ℕ) : ∑ p : PauliLabel k, x ^ (k - pauli_size p) = (x + 3) ^ k := by
  simp_rw [sum_pow_pauli_size_prod_per_qubit]
  rw [← Equiv.sum_comp (sum_pow_pauli_size_equiv k)]
  have h_prod : (∑ g : Fin k → ZMod 2 × ZMod 2, ∏ i : Fin k,
      (if (sum_pow_pauli_size_equiv k g).1 i = 0 then (if (sum_pow_pauli_size_equiv k g).2 i = 0 then x else 1) else 1))
    = (∑ g : Fin k → ZMod 2 × ZMod 2, ∏ i : Fin k,
      (if (g i).1 = 0 then (if (g i).2 = 0 then x else 1) else 1)) := by
    rfl
  rw [h_prod]
  have h_swap := (@Fintype.prod_sum (Fin k) ℕ _ _ _ (fun _ => ZMod 2 × ZMod 2) _
    (fun _ c => if c.1 = 0 then if c.2 = 0 then x else 1 else 1)).symm
  rw [h_swap]
  simp_rw [sum_pow_pauli_size_sum_zmod2_sq]
  rw [prod_const, card_univ, Fintype.card_fin]
