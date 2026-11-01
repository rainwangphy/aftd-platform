import AFTD.Prelude

/-!
# finite_function_exists_positive_period

Topic: fair_division   Node: 13ac616c164f

Provenance: helper lemma. Helper for efx_four_agents_additive_exists (OP-7), campaign session IN-404, 2026-11-01. Standard cycle elimination and ordered insertion, arXiv:1707.04769v3 Lemma 6.1 and Appendix B; no novelty claim.

Every endomorphism of a finite nonempty type has a periodic point with a strictly positive period.
-/

open Function Finset

theorem finite_function_exists_positive_period {α : Type*} [Finite α] [Nonempty α] (f : α → α) :
    ∃ k, 0 < k ∧ ∃ x, Function.IsPeriodicPt f k x := by
  classical
  let x : α := Classical.choice inferInstance
  obtain ⟨a, b, heq, hab⟩ := Function.not_injective_iff.mp
    (not_injective_infinite_finite (f^[·] x))
  wlog hlt : a < b generalizing a b
  · exact this b a heq.symm hab.symm (lt_of_le_of_ne (Nat.le_of_not_gt hlt) hab.symm)
  refine ⟨b-a, Nat.sub_pos_of_lt hlt, f^[a] x, ?_⟩
  change f^[b-a] (f^[a] x) = f^[a] x
  rw [← Function.iterate_add_apply, Nat.sub_add_cancel hlt.le]
  exact heq.symm
