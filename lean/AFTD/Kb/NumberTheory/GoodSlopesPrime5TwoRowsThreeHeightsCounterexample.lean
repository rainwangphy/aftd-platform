import AFTD.Prelude

/-!
# good_slopes_prime5_two_rows_three_heights_counterexample

Topic: elementary_number_theory   Node: ed714e7b51bf

Provenance: helper lemma. Counterexample identified in computation 27596 for the OP-1027 fiber investigation.

There are five points over Z/5 with two specified injective directions, at most three distinct second coordinates, and no containing affine line. This refutes the proposed two-direction strengthening of the field-five step.
-/

theorem good_slopes_prime5_two_rows_three_heights_counterexample :
    ∃ S : Finset (ZMod 5 × ZMod 5),
      S.card = 5 ∧
      (S.image fun p => p.2 + p.1).card = 5 ∧
      (S.image fun p => p.2 + 2*p.1).card = 5 ∧
      (S.image fun p => p.2).card ≤ 3 ∧
      (¬ ∃ a b : ZMod 5, ∀ p ∈ S, p.2 + a*p.1 = b) ∧
      (¬ ∃ x : ZMod 5, ∀ p ∈ S, p.1 = x) := by
  let S : Finset (ZMod 5 × ZMod 5) := {(0,0), (0,1), (0,2), (1,2), (4,0)}
  refine ⟨S, by decide, by decide, by decide, by decide, ?_, ?_⟩
  · rintro ⟨a,b,h⟩
    have h0 := h (0,0) (by decide)
    have h1 := h (0,1) (by decide)
    simp only [mul_zero, add_zero] at h0 h1
    exact (by decide : (0 : ZMod 5) ≠ 1) (h0.trans h1.symm)
  · rintro ⟨x,h⟩
    have h0 := h (0,0) (by decide)
    have h1 := h (1,2) (by decide)
    exact (by decide : (0 : ZMod 5) ≠ 1) (h0.trans h1.symm)
