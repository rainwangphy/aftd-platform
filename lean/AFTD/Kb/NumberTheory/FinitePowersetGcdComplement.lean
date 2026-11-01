import AFTD.Prelude

/-!
# finite_powerset_gcd_complement

Topic: elementary_number_theory   Node: ff826bf8f94f

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

Complementing each subset inside a finite universe preserves the gcd of the function values over all subsets.
-/

theorem finite_powerset_gcd_complement {α : Type*} [DecidableEq α]
    (U : Finset α) (f : Finset α → ℕ) :
    U.powerset.gcd (fun A => f (U \ A)) = U.powerset.gcd f := by
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd_iff.mpr
    intro A hA
    have hc : U \ A ∈ U.powerset := Finset.mem_powerset.mpr Finset.sdiff_subset
    have hd := Finset.gcd_dvd (f := fun A => f (U \ A)) hc
    simpa only [Finset.sdiff_sdiff_eq_self (Finset.mem_powerset.mp hA)] using hd
  · apply Finset.dvd_gcd_iff.mpr
    intro A hA
    exact Finset.gcd_dvd (Finset.mem_powerset.mpr Finset.sdiff_subset)
