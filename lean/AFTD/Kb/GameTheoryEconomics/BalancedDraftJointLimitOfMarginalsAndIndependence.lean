import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsBalancedSchedule
import AFTD.Kb.GameTheoryEconomics.BalancedDraftScaledUtility
import AFTD.Kb.GameTheoryEconomics.BalancedDraftInputLaw
import AFTD.Kb.GameTheoryEconomics.BalancedDraftGaussianLaw
import AFTD.Kb.GameTheoryEconomics.BalancedDraftJointGaussianLaw

/-!
# balanced_draft_joint_limit_of_marginals_and_independence

Topic: fair_division   Node: b5a11c1b4b12

Provenance: helper lemma. Finite-product reduction for the joint Gaussian limit in OP-1493.

If every agent has the stated marginal Gaussian limit under balanced schedules, and the scaled utilities are jointly independent for every finite number of goods and every deterministic schedule, then the joint Gaussian limit holds under every balanced schedule.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped Topology

theorem balanced_draft_joint_limit_of_marginals_and_independence
  (hmarg : ∀ (n : ℕ), 2 ≤ n → ∀ (schedule : ∀ m, Fin m → Fin n),
    (∀ m, is_balanced_schedule n m (schedule m)) → ∀ i : Fin n,
    (∀ m, AEMeasurable (fun v => balanced_draft_scaled_utility n m (schedule m) v i)
      (balanced_draft_input_law n m : Measure (Fin n → Fin m → ℝ))) ∧
    TendstoInDistribution (fun m v => balanced_draft_scaled_utility n m (schedule m) v i) atTop
      (fun x : ℝ => x)
      (fun m => (balanced_draft_input_law n m : Measure (Fin n → Fin m → ℝ)))
      (balanced_draft_gaussian_law n : Measure ℝ))
  (hindep : ∀ (n m : ℕ) (s : Fin m → Fin n),
    iIndepFun (fun i v => balanced_draft_scaled_utility n m s v i)
      (balanced_draft_input_law n m : Measure (Fin n → Fin m → ℝ))) :
  ∀ (n : ℕ), 2 ≤ n → ∀ (schedule : ∀ m, Fin m → Fin n),
    (∀ m, is_balanced_schedule n m (schedule m)) →
    (∀ m, AEMeasurable (balanced_draft_scaled_utility n m (schedule m))
      (balanced_draft_input_law n m : Measure (Fin n → Fin m → ℝ))) ∧
    TendstoInDistribution (fun m => balanced_draft_scaled_utility n m (schedule m)) atTop
      (fun x : Fin n → ℝ => x)
      (fun m => (balanced_draft_input_law n m : Measure (Fin n → Fin m → ℝ)))
      (balanced_draft_joint_gaussian_law n : Measure (Fin n → ℝ)) := by
  intro n hn schedule hs
  have hmeas : ∀ m i, AEMeasurable (fun v => balanced_draft_scaled_utility n m (schedule m) v i)
      (balanced_draft_input_law n m : Measure (Fin n → Fin m → ℝ)) := by
    intro m i
    exact (hmarg n hn schedule hs i).1 m
  have hvec : ∀ m, AEMeasurable (balanced_draft_scaled_utility n m (schedule m))
      (balanced_draft_input_law n m : Measure (Fin n → Fin m → ℝ)) := by
    intro m
    exact aemeasurable_pi_lambda _ (fun i => hmeas m i)
  let marginal (m : ℕ) (i : Fin n) : ProbabilityMeasure ℝ :=
    ⟨(balanced_draft_input_law n m : Measure (Fin n → Fin m → ℝ)).map
      (fun v => balanced_draft_scaled_utility n m (schedule m) v i),
     Measure.isProbabilityMeasure_map (hmeas m i)⟩
  have hm : Tendsto (fun m => fun i => marginal m i) atTop
      (𝓝 (fun _ : Fin n => balanced_draft_gaussian_law n)) := by
    apply tendsto_pi_nhds.mpr
    intro i
    have hi := (hmarg n hn schedule hs i).2.tendsto
    have heta : (⟨(balanced_draft_gaussian_law n : Measure ℝ).map (fun x => x),
        Measure.isProbabilityMeasure_map aemeasurable_id⟩ : ProbabilityMeasure ℝ) =
        balanced_draft_gaussian_law n := by
      apply Subtype.ext
      simp
    simpa only [marginal, heta] using hi
  have hp : Tendsto (fun m => ProbabilityMeasure.pi (marginal m)) atTop
      (𝓝 (balanced_draft_joint_gaussian_law n)) := by
    have hc := ProbabilityMeasure.continuous_pi.continuousAt.tendsto.comp hm
    simpa [balanced_draft_joint_gaussian_law, Function.comp_def] using hc
  have hmap (m : ℕ) :
      (⟨(balanced_draft_input_law n m : Measure (Fin n → Fin m → ℝ)).map
          (balanced_draft_scaled_utility n m (schedule m)),
        Measure.isProbabilityMeasure_map (hvec m)⟩ : ProbabilityMeasure (Fin n → ℝ)) =
      ProbabilityMeasure.pi (marginal m) := by
    apply Subtype.ext
    exact (hindep n m (schedule m)).map_fun_eq_pi_map (fun i => hmeas m i)
  refine ⟨hvec, ⟨hvec, aemeasurable_id, ?_⟩⟩
  have heta :
      (⟨(balanced_draft_joint_gaussian_law n : Measure (Fin n → ℝ)).map (fun x => x),
        Measure.isProbabilityMeasure_map aemeasurable_id⟩ : ProbabilityMeasure (Fin n → ℝ)) =
      balanced_draft_joint_gaussian_law n := by
    apply Subtype.ext
    simp
  simpa only [hmap, heta] using hp
