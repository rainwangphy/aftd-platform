import AFTD.Prelude

/-!
# restricted_cycle_same_cycle_card_bounds

Topic: elementary_number_theory   Node: 7af90588cf2e

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

The SameCycle class of any point of Fin n has cardinality at least 1 and at most n.
-/

theorem restricted_cycle_same_cycle_card_bounds (n : ℕ) (σ : Equiv.Perm (Fin n)) (x : Fin n) :
    (Finset.univ.filter fun y => σ.SameCycle x y).card ∈ Finset.Icc 1 n := by
  classical
  apply Finset.mem_Icc.mpr
  constructor
  · apply Finset.one_le_card.mpr
    exact ⟨x, by simp [Equiv.Perm.SameCycle.refl]⟩
  · exact (Finset.card_le_card (Finset.filter_subset _ _)).trans_eq (by simp)
