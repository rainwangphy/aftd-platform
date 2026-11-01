import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCycleAllSameCycleOfShort

/-!
# restricted_cycle_card_eq_of_short

Topic: elementary_number_theory   Node: e8c220d28d40

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

If n is less than 2(r+1), the cycle containing any point of a permutation avoiding lengths 1 through r has cardinality n.
-/

theorem restricted_cycle_card_eq_of_short (r n : ℕ) (hn : n < 2 * (r+1))
    (σ : Equiv.Perm (Fin n))
    (hσ : ∀ x : Fin n,
      (Finset.univ.filter fun y => σ.SameCycle x y).card ∉ Finset.Icc 1 r)
    (x : Fin n) : (Finset.univ.filter fun y => σ.SameCycle x y).card = n := by
  classical
  have h : (Finset.univ.filter fun y => σ.SameCycle x y) = Finset.univ := by
    ext y
    simp [restricted_cycle_all_same_cycle_of_short r n hn σ hσ x y]
  rw [h]
  simp
