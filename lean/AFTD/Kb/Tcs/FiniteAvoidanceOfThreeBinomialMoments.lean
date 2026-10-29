import AFTD.Prelude

/-!
# finite_avoidance_of_three_binomial_moments

Topic: graphs   Node: 47a7d409e948

Provenance: helper lemma. Certificate-soundness and finite averaging helpers for the OP-306 campaign on arXiv:2610.22142, Sections 3.3.1 and 3.3.2. The thirteen-vertex equivalence is a reduction, not a proof of the conjectured equality; the moment criterion supplies no unproved universal numerical hypothesis.

For a natural-valued function d on a finite sample space J, if the sum of d plus the sum of binomial(d,3) is strictly less than the cardinality of J plus the sum of binomial(d,2), then d is zero at some sample.
-/

open scoped BigOperators Classical
set_option maxHeartbeats 1600000
set_option maxRecDepth 100000

theorem finite_avoidance_of_three_binomial_moments {J : Type*} [Fintype J]
    (d : J → ℕ)
    (h : (∑ j : J, d j) + (∑ j : J, (d j).choose 3) <
      Fintype.card J + (∑ j : J, (d j).choose 2)) : ∃ j, d j = 0 := by
  by_contra! hno
  have pointwise : ∀ j, 1+(d j).choose 2 ≤ d j+(d j).choose 3 := by
    intro j
    obtain ⟨r,he⟩ := Nat.exists_eq_succ_of_ne_zero (hno j)
    rw [he]
    simp only [Nat.choose_succ_succ,Nat.choose_one_right]
    change 1+(r+r.choose 2) ≤ (r+1)+(r.choose 2+r.choose 3)
    omega
  have hi := Finset.sum_le_sum (fun j (_ : j ∈ (Finset.univ : Finset J)) => pointwise j)
  simp only [Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,nsmul_eq_mul,mul_one] at hi
  have hi' : Fintype.card J+(∑ j : J, (d j).choose 2) ≤
      (∑ j : J, d j)+(∑ j : J, (d j).choose 3) := by exact_mod_cast hi
  omega
