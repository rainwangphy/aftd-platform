import AFTD.Prelude

/-!
# condorcet_stationary_telescoping_general

Topic: social_choice   Node: 7ea9b461446d

Provenance: helper lemma. IN-341 generic supporting algebra for the OP-19 tournament-consistent stationarity diagnostic. Generalizes condorcet_stationary_telescoping_bound from56 states to arbitrary q; no new election result or research advance.

On an arbitrary finite three-successor transition graph, suppose a natural potential has local conservation lower bound K against scale C times a natural score, with K positive and C at most twice K. Every natural stationary weighting then has total weight at most twice its weighted score. This generalizes the existing56-state helper to any number of states.
-/

private theorem condorcet_stationary_telescoping_general_swap
    {q : ℕ} (next : Fin q → Fin 3 → Fin q) (p w : Fin q → ℕ) :
    (∑ j, p j * ∑ i, ∑ k : Fin 3, if next i k = j then w i else 0) =
      ∑ i, ∑ k : Fin 3, p (next i k) * w i := by
  open Finset in
  simp_rw [mul_sum]
  rw [sum_comm]
  refine sum_congr rfl fun i _ => ?_
  rw [sum_comm]
  refine sum_congr rfl fun k _ => ?_
  rw [show (∑ x, p x * (if next i k = x then w i else 0))
        = ∑ x, (if next i k = x then p x * w i else 0) by
        refine sum_congr rfl fun x _ => ?_
        by_cases h : next i k = x <;> simp [h]]
  rw [sum_ite_eq]
  simp

theorem condorcet_stationary_telescoping_general
    (q C K : ℕ) (hK : 0 < K) (hCK : C ≤ 2*K)
    (next : Fin q → Fin 3 → Fin q) (p score w : Fin q → ℕ)
    (hlocal : ∀ i, K+3*p i ≤ C*score i+∑ k : Fin 3, p (next i k))
    (hw : ∀ j, 3*w j = ∑ i, ∑ k : Fin 3, if next i k=j then w i else 0) :
    (∑ i,w i) ≤ 2*∑ i,score i*w i := by
  open Finset in
  have h_pot : (∑ i, 3 * p i * w i) = ∑ i, ∑ k : Fin 3, p (next i k) * w i := by
    have h1 : (∑ i, 3 * p i * w i) = ∑ i, p i * (3 * w i) := by
      refine sum_congr rfl fun i _ => by ring
    rw [h1]
    simp_rw [hw]
    exact condorcet_stationary_telescoping_general_swap next p w
  have h_sum_le : (∑ i, (K + 3 * p i) * w i) ≤
      ∑ i, (C * score i + ∑ k : Fin 3, p (next i k)) * w i := by
    refine Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right (w i) (hlocal i)
  have h_lhs : (∑ i, (K + 3 * p i) * w i) = K * (∑ i, w i) + ∑ i, 3 * p i * w i := by
    open Finset in simp_rw [add_mul, sum_add_distrib, mul_sum]
  have h_rhs : (∑ i, (C * score i + ∑ k : Fin 3, p (next i k)) * w i) =
      C * (∑ i, score i * w i) + ∑ i, ∑ k : Fin 3, p (next i k) * w i := by
    open Finset in simp_rw [add_mul, sum_add_distrib, sum_mul, mul_assoc, mul_sum]
  rw [h_lhs, h_rhs, h_pot] at h_sum_le
  have hKC : K * (∑ i, w i) ≤ C * (∑ i, score i * w i) :=
    Nat.le_of_add_le_add_right h_sum_le
  have h1 : C * (∑ i, score i * w i) ≤ (2 * K) * (∑ i, score i * w i) :=
    Nat.mul_le_mul_right (∑ i, score i * w i) hCK
  have h2 : K * (∑ i, w i) ≤ (2 * K) * (∑ i, score i * w i) := hKC.trans h1
  have h3 : (2 * K) * (∑ i, score i * w i) = K * (2 * ∑ i, score i * w i) := by ring
  rw [h3] at h2
  exact Nat.le_of_mul_le_mul_left h2 hK
