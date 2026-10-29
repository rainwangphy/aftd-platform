import AFTD.Prelude

/-!
# condorcet_stationary_telescoping_bound

Topic: social_choice   Node: cc0977faf0e5

Provenance: helper lemma. step towards condorcet_stationary_weight_restriction_obstruction

On any 3-regular directed transition graph on 56 vertices, if a potential vector p and positive bound K satisfy K + 3 * p i <= C * score i + sum_k p(next i k) for all i, and C <= 2 * K, then every nonnegative integer stationary weighting w satisfies sum w <= 2 * sum (score i * w i).
-/

lemma condorcet_stationary_telescoping_bound_swap
    (next : Fin 56 → Fin 3 → Fin 56) (p : Fin 56 → ℕ) (w : Fin 56 → ℕ) :
    (∑ j : Fin 56, p j * (∑ i : Fin 56, ∑ k : Fin 3, if next i k = j then w i else 0)) =
    ∑ i : Fin 56, ∑ k : Fin 3, p (next i k) * w i := by
  open Finset in
  simp_rw [mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  have : (fun j => p j * (if next i k = j then w i else 0)) =
         (fun j => if next i k = j then p (next i k) * w i else 0) := by
    funext j
    split_ifs with h
    · subst h; rfl
    · rw [mul_zero]
  rw [this]
  rw [Finset.sum_ite_eq]
  simp

/-- Telescoping conservation bound for stationary weights on a 3-regular graph. -/
theorem condorcet_stationary_telescoping_bound
    (C K : ℕ) (hK : 0 < K) (hCK : C ≤ 2 * K)
    (next : Fin 56 → Fin 3 → Fin 56)
    (p : Fin 56 → ℕ) (score : Fin 56 → ℕ)
    (hlocal : ∀ i, K + 3 * p i ≤ C * score i + ∑ k : Fin 3, p (next i k))
    (w : Fin 56 → ℕ)
    (hw : ∀ j, 3 * w j = ∑ i, ∑ k : Fin 3, if next i k = j then w i else 0) :
    (∑ i, w i) ≤ 2 * ∑ i, score i * w i := by
  open Finset in
  have h_pot : (∑ i, 3 * p i * w i) = ∑ i, ∑ k : Fin 3, p (next i k) * w i := by
    have h1 : (∑ i, 3 * p i * w i) = ∑ i, p i * (3 * w i) := by
      refine sum_congr rfl fun i _ => by ring
    rw [h1]
    simp_rw [hw]
    exact condorcet_stationary_telescoping_bound_swap next p w
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
