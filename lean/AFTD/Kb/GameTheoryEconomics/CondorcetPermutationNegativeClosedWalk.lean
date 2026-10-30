import AFTD.Prelude

/-!
# condorcet_permutation_negative_closed_walk

Topic: social_choice   Node: 5baf5b01683f

Provenance: helper lemma. IN-380, OP-19 campaign session8, 2026-10-30. Supporting reduction from the proved strict-half circulation bridge. Scratch ClosedWalk.lean passed trusted-axiom checking. Standard finite matching and orbit averaging; no research novelty or new election bound is claimed.

For a permutation of a finite type and real costs with strictly negative total, some point has a nonempty periodic orbit segment of strictly negative summed cost. Repetition of an orbit is allowed; no simple-cycle claim is made.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_permutation_negative_closed_walk
    {V : Type*} [Fintype V] (e : Equiv.Perm V) (c : V → ℝ)
    (hc : (∑ x, c x) < 0) :
    ∃ l : ℕ, 0 < l ∧ ∃ x : V,
      (e^l) x = x ∧ (∑ i ∈ range l, c ((e^i) x)) < 0 := by
  classical
  let l := orderOf e
  have hl : 0 < l := orderOf_pos e
  have hsum : (∑ x, ∑ i ∈ range l, c ((e^i) x)) = (l : ℝ) * ∑ x, c x := by
    rw [sum_comm]
    simp only [Equiv.sum_comp]
    simp
  have hneg : (∑ x, ∑ i ∈ range l, c ((e^i) x)) < 0 := by
    rw [hsum]
    exact mul_neg_of_pos_of_neg (by exact_mod_cast hl) hc
  obtain ⟨x,hx⟩ : ∃ x, (∑ i ∈ range l, c ((e^i) x)) < 0 := by
    by_contra hbad
    push_neg at hbad
    have hnon : 0 ≤ ∑ x, ∑ i ∈ range l, c ((e^i) x) := sum_nonneg (fun x _ => hbad x)
    linarith
  refine ⟨l,hl,x,?_,hx⟩
  simp [l,pow_orderOf_eq_one]
