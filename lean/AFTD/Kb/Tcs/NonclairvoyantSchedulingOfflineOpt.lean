import AFTD.Prelude

/-!
# nonclairvoyant_scheduling_offline_opt

Topic: online_algorithms   Node: 7e2a5ffabea1

Provenance: formalization of a published result. Source: arXiv:2610.29037 Section 4 (text before Lemma 4.2)

For any natural number n and job processing vector w : Fin n → ℝ, the offline optimal total completion time nonclairvoyant_scheduling_offline_opt w is the minimum over all permutations π of Fin n of the sum ∑ i : Fin n, ((n : ℝ) - (i : ℝ)) * w (π i).
-/

/-- The offline optimal total completion time for jobs with processing times vector w in R^n. -/
noncomputable def nonclairvoyant_scheduling_offline_opt {n : ℕ} (w : Fin n → ℝ) : ℝ := Finset.univ.inf' ⟨1, Finset.mem_univ 1⟩
    (fun π : Equiv.Perm (Fin n) => ∑ i : Fin n, ((n : ℝ) - (i : ℝ)) * w (π i))
