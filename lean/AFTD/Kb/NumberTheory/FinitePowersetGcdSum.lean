import AFTD.Prelude
import AFTD.Kb.NumberTheory.FinitePowersetDvdSumIff

/-!
# finite_powerset_gcd_sum

Topic: elementary_number_theory   Node: 82f9ae8e01f7

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

The gcd of the sums of f over all subsets of each subset A of U equals the gcd of f over all subsets of U.
-/

theorem finite_powerset_gcd_sum {α : Type*} [DecidableEq α]
    (U : Finset α) (f : Finset α → ℕ) :
    U.powerset.gcd (fun A => ∑ B ∈ A.powerset, f B) = U.powerset.gcd f := by
  apply Nat.dvd_antisymm
  · apply Finset.dvd_gcd_iff.mpr
    have h : ∀ A ⊆ U, U.powerset.gcd (fun A => ∑ B ∈ A.powerset, f B) ∣
        ∑ B ∈ A.powerset, f B := by
      intro A hAU
      exact Finset.gcd_dvd (Finset.mem_powerset.mpr hAU)
    intro A hA
    exact (finite_powerset_dvd_sum_iff U f _).mp h A (Finset.mem_powerset.mp hA)
  · apply Finset.dvd_gcd_iff.mpr
    intro A hA
    apply Finset.dvd_sum
    intro B hB
    exact Finset.gcd_dvd (Finset.mem_powerset.mpr
      ((Finset.mem_powerset.mp hB).trans (Finset.mem_powerset.mp hA)))
