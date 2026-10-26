import AFTD.Prelude
import AFTD.Kb.Tcs.NonclairvoyantSchedulingOfflineOpt

/-!
# nonclairvoyant_scheduling_offline_opt_superadditive

Topic: online_algorithms   Node: c1844c8da063

Provenance: formalization of a published result. Source: arXiv:2610.29037 Lemma 4.2 proof step (1)

For any natural number n and job processing vectors a, z : Fin n → ℝ, the offline optimal total completion time satisfies superadditivity: nonclairvoyant_scheduling_offline_opt a + nonclairvoyant_scheduling_offline_opt z ≤ nonclairvoyant_scheduling_offline_opt (a + z).
-/

/-- Superadditivity of the offline optimal total completion time: OPT(a + z) >= OPT(a) + OPT(z). -/
theorem nonclairvoyant_scheduling_offline_opt_superadditive {n : ℕ}
    (a z : Fin n → ℝ) :
    nonclairvoyant_scheduling_offline_opt a + nonclairvoyant_scheduling_offline_opt z ≤
      nonclairvoyant_scheduling_offline_opt (a + z) := by
  simp only [nonclairvoyant_scheduling_offline_opt]
  have key : ∀ π : Equiv.Perm (Fin n),
      (∑ i : Fin n, ((n : ℝ) - (i : ℝ)) * (a + z) (π i))
        = (∑ i : Fin n, ((n : ℝ) - (i : ℝ)) * a (π i))
          + (∑ i : Fin n, ((n : ℝ) - (i : ℝ)) * z (π i)) := by
    intro π
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl ?_
    intro i _
    simp only [Pi.add_apply, mul_add]
  refine Finset.le_inf' _ _ (fun π hπ => ?_)
  have h1 := Finset.inf'_le
    (fun π : Equiv.Perm (Fin n) => ∑ i : Fin n, ((n : ℝ) - (i : ℝ)) * a (π i)) hπ
  have h2 := Finset.inf'_le
    (fun π : Equiv.Perm (Fin n) => ∑ i : Fin n, ((n : ℝ) - (i : ℝ)) * z (π i)) hπ
  rw [key π]
  linarith
