import AFTD.Prelude

/-!
# finite_powerset_dvd_sum_iff

Topic: elementary_number_theory   Node: 2b822365c4a2

Provenance: helper lemma. Helper for global_gcd_agreement_r_ge_four, OP-746, inbox IN-440. arXiv:2610.40342v1 Proposition 11.3(i) and Appendix A.5 give the support decomposition. No novelty claim; the uniform conjecture in Question 14.10 remains open.

For a natural-valued function on the subsets of a finite set U, a natural number divides every subset sum over powersets if and only if it divides every function value on a subset of U.
-/

theorem finite_powerset_dvd_sum_iff {α : Type*} [DecidableEq α]
    (U : Finset α) (f : Finset α → ℕ) (d : ℕ) :
    (∀ A ⊆ U, d ∣ ∑ B ∈ A.powerset, f B) ↔
    (∀ A ⊆ U, d ∣ f A) := by
  constructor
  · intro h A
    induction A using Finset.strongInductionOn with
    | _ A ih =>
      intro hAU
      have hrest : d ∣ ∑ B ∈ A.powerset.erase A, f B := by
        apply Finset.dvd_sum
        intro B hB
        obtain ⟨hne, hsub⟩ := Finset.mem_erase.mp hB
        have hBA : B ⊆ A := Finset.mem_powerset.mp hsub
        exact ih B (Finset.ssubset_iff_subset_ne.mpr ⟨hBA, hne⟩) (hBA.trans hAU)
      have heq := Finset.sum_erase_add A.powerset f (Finset.mem_powerset_self A)
      have hall := h A hAU
      rw [← heq] at hall
      exact (Nat.dvd_add_iff_left hrest).mpr (by simpa only [Nat.add_comm] using hall)
  · intro h A hAU
    apply Finset.dvd_sum
    intro B hB
    exact h B ((Finset.mem_powerset.mp hB).trans hAU)
