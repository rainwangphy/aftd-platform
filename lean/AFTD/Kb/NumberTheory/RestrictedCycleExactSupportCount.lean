import AFTD.Prelude
import AFTD.Kb.NumberTheory.RestrictedCycleLengthSupport

/-!
# restricted_cycle_exact_support_count

Topic: elementary_number_theory   Node: 5d4af8f2c639

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

The number of permutations of Fin n with set of distinct cycle lengths exactly P, including fixed points as cycles of length 1.
-/

noncomputable def restricted_cycle_exact_support_count (n : ℕ) (P : Finset ℕ) : ℕ := by
  classical
  exact (Finset.univ.filter fun σ : Equiv.Perm (Fin n) => restricted_cycle_length_support n σ = P).card
