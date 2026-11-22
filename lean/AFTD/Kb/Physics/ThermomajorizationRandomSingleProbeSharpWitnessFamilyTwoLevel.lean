import AFTD.Prelude
import AFTD.Kb.Physics.ThermomajorizationWitnessX
import AFTD.Kb.Physics.ThermomajorizationWitnessY
import AFTD.Kb.Physics.ThermomajorizationExpectedMissedError
import AFTD.Kb.Physics.ThermomajorizationRandomProbeWorstError
import AFTD.Kb.Physics.ThermomajorizationDiff
import AFTD.Kb.Physics.ThermomajorizationProbeError
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# thermomajorization_random_single_probe_sharp_witness_family_two_level

Topic: quantum_mechanics   Node: 5cd332f663ff

Provenance: helper lemma. OP-2138

For dimension n = 2 and any probability distribution q ∈ stdSimplex ℝ (Finset.Ioo 0 2), there exist integers a, j, b with a < j ∧ j < b ∧ b ≤ 2 such that the expected missed conversion error thermomajorization_expected_missed_error 2 q (thermomajorization_witness_x 2 a j b) (thermomajorization_witness_y 2 j) equals thermomajorization_random_probe_worst_error 2 q.
-/

/-- Thermomajorization random single probe sharp witness family holds for n = 2. -/
theorem thermomajorization_random_single_probe_sharp_witness_family_two_level :
    ∀ (q : Finset.Ioo 0 2 → ℝ) (hq : q ∈ stdSimplex ℝ (Finset.Ioo 0 2)),
      ∃ a j b, a < j ∧ j < b ∧ b ≤ 2 ∧
        thermomajorization_expected_missed_error 2 q
          (thermomajorization_witness_x 2 a j b) (thermomajorization_witness_y 2 j) =
        thermomajorization_random_probe_worst_error 2 q := by
  intro q hq
  have hq1 : q ⟨1, by decide⟩ = 1 := by
    have hsum : (∑ k : ↥(Finset.Ioo 0 2), q k) = q ⟨1, by decide⟩ := by
      have huniv : (Finset.univ : Finset ↥(Finset.Ioo 0 2)) = {⟨1, by decide⟩} := by
        ext z
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        obtain ⟨v, hv⟩ := z
        simp only [Finset.mem_Ioo] at hv
        have : v = 1 := by omega
        subst this
        rfl
      rw [huniv, Finset.sum_singleton]
    rw [← hsum]
    exact hq.2
  have hconst : ∀ x y : Fin 2 → ℝ, thermomajorization_expected_missed_error 2 q x y = 0 := by
    intro x y
    have hprobe : thermomajorization_probe_error 2 (Finset.Ioo 0 2) x y =
        max 0 (thermomajorization_diff x y 1) := by
      unfold thermomajorization_probe_error
      rw [show (Finset.Ioo 0 2 : Finset ℕ) = {1} from by decide]
      simp only [Finset.image_singleton]
      rw [Finset.max'_insert (H := Finset.singleton_nonempty _), Finset.max'_singleton]
    have hsum2 : (∑ k : ↥(Finset.Ioo 0 2), q k * max 0 (thermomajorization_diff x y (k : ℕ)))
        = max 0 (thermomajorization_diff x y 1) := by
      have huniv : (Finset.univ : Finset ↥(Finset.Ioo 0 2)) = {⟨1, by decide⟩} := by
        ext z
        simp only [Finset.mem_univ, Finset.mem_singleton, true_iff]
        obtain ⟨v, hv⟩ := z
        simp only [Finset.mem_Ioo] at hv
        have : v = 1 := by omega
        subst this
        rfl
      rw [huniv, Finset.sum_singleton, hq1, one_mul]
    unfold thermomajorization_expected_missed_error
    rw [hprobe, hsum2]
    ring
  have hworst : thermomajorization_random_probe_worst_error 2 q = 0 := by
    unfold thermomajorization_random_probe_worst_error
    simp only [hconst]
    simp
  refine ⟨0, 1, 2, by norm_num, by norm_num, by norm_num, ?_⟩
  rw [hconst, hworst]
