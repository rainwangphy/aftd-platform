import AFTD.Prelude

/-!
# restricted_cycle_length_support

Topic: elementary_number_theory   Node: 428a06d0fe41

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

The finite set of distinct cycle lengths of a permutation of Fin n, defined by the cardinalities of its SameCycle equivalence classes. Fixed points contribute length 1.
-/

noncomputable def restricted_cycle_length_support (n : ℕ) (σ : Equiv.Perm (Fin n)) : Finset ℕ := by
  classical
  exact Finset.univ.image (fun x => (Finset.univ.filter fun y => σ.SameCycle x y).card)
