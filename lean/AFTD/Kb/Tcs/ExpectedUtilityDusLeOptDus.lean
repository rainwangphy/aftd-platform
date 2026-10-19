import AFTD.Prelude
import AFTD.Kb.Tcs.OptDUS
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.Support

/-!
# expected_utility_dus_le_opt_dus

Topic: online_algorithms   Node: 13f7e0456af4

Provenance: helper lemma. step towards op182_deferred_to_deadline_beyond_half_against_stopping

For any Pandora's problem instance with deadlines `inst` and any valid policy `π`, `expectedUtilityDUS inst π ≤ optDUS inst`.
-/

lemma expected_utility_dus_le_opt_dus_foldl_max_le {α : Type*} :
    ∀ (l : List (α × ℝ)) (x M : ℝ), (∀ bv ∈ l, bv.2 ≤ M) →
      List.foldl (fun acc bv => max acc bv.2) x l ≤ max x M
  | [], x, M, _ => by simp
  | hd :: tl, x, M, h => by
      have h1 : hd.2 ≤ M := h hd (by simp)
      simp only [List.foldl_cons]
      refine le_trans (expected_utility_dus_le_opt_dus_foldl_max_le tl (max x hd.2) M
        (fun bv hbv => h bv (List.mem_cons_of_mem _ hbv))) ?_
      rw [max_assoc, max_eq_right h1]

lemma expected_utility_dus_le_opt_dus_aux_bound (inst : PandoraDeadlineInstance) (M : ℝ)
    (hM0 : 0 ≤ M) (hMv : ∀ (i : Fin inst.n) (v : ℝ), v ∈ (inst.dist i).support → v ≤ M) :
    ∀ (a : AdaptivePolicy inst.n) (hist : List (Fin inst.n × ℝ)),
      (∀ bv ∈ hist, bv.2 ≤ M) → expectedUtilityDUS.aux inst hist a ≤ M := by
  intro a
  induction a using AdaptivePolicy.rec with
  | stop =>
      intro hist hh
      rw [show expectedUtilityDUS.aux inst hist (AdaptivePolicy.stop : AdaptivePolicy inst.n)
          = List.foldl (fun acc bv => max acc bv.2) 0 hist from rfl]
      exact le_trans (expected_utility_dus_le_opt_dus_foldl_max_le hist 0 M hh) (by rw [max_eq_right hM0])
  | openBox b cont ih =>
      intro hist hh
      rw [show expectedUtilityDUS.aux inst hist (AdaptivePolicy.openBox b cont) =
        ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
          expectedUtilityDUS.aux inst ((b, v) :: hist) (cont v) - inst.cost b from rfl]
      have hsum : ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
            expectedUtilityDUS.aux inst ((b, v) :: hist) (cont v) ≤ M := by
        have h1 : ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
            expectedUtilityDUS.aux inst ((b, v) :: hist) (cont v)
            ≤ ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v * M := by
          apply Finset.sum_le_sum
          intro v hv
          apply mul_le_mul_of_nonneg_left _ ((inst.dist b).prob_nonneg v hv)
          exact ih v ((b, v) :: hist) (fun bv hbv => by
            rcases List.mem_cons.mp hbv with hmem | hmem
            · rw [hmem]; exact hMv b v hv
            · exact hh bv hmem)
        calc ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v *
              expectedUtilityDUS.aux inst ((b, v) :: hist) (cont v)
            ≤ ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v * M := h1
          _ = (∑ v ∈ (inst.dist b).support, (inst.dist b).prob v) * M := by
                rw [Finset.sum_mul]
          _ = M := by rw [(inst.dist b).sum_prob_one, one_mul]
      linarith [inst.cost_nonneg b]

lemma expected_utility_dus_le_opt_dus_bddAbove (inst : PandoraDeadlineInstance) :
    BddAbove (Set.range fun π : AdaptivePolicy inst.n => expectedUtilityDUS inst π) := by
  refine ⟨∑ i : Fin inst.n, ∑ v ∈ (inst.dist i).support, v, ?_⟩
  rintro _ ⟨π, rfl⟩
  apply expected_utility_dus_le_opt_dus_aux_bound inst _ ?_ ?_ π [] (by simp)
  · exact Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun v hv => (inst.dist i).val_nonneg v hv
  · intro i v hv
    refine le_trans (Finset.single_le_sum (f := fun v => v)
      (fun v hv => (inst.dist i).val_nonneg v hv) hv) ?_
    exact Finset.single_le_sum (f := fun i => ∑ v ∈ (inst.dist i).support, v)
      (fun i _ => Finset.sum_nonneg fun v hv => (inst.dist i).val_nonneg v hv) (Finset.mem_univ i)

/-- For any Pandora's problem instance with deadlines and any valid adaptive policy, its expected utility under deferred-until-stopping commitment is at most optDUS. -/
theorem expected_utility_dus_le_opt_dus (inst : PandoraDeadlineInstance) (π : AdaptivePolicy inst.n)
    (hπ : IsValidPolicy inst π) :
    expectedUtilityDUS inst π ≤ optDUS inst := by
  have hbdd : BddAbove (Set.range fun π : AdaptivePolicy inst.n =>
      ⨆ (_ : IsValidPolicy inst π), expectedUtilityDUS inst π) := by
    refine BddAbove.range_iSup_of_iUnion_range ?_
    obtain ⟨B, hB⟩ := expected_utility_dus_le_opt_dus_bddAbove inst
    refine ⟨B, ?_⟩
    intro x hx
    simp only [Set.mem_iUnion, Set.mem_range] at hx
    obtain ⟨π', -, rfl⟩ := hx
    exact hB (Set.mem_range_self π')
  unfold optDUS
  have h1 : expectedUtilityDUS inst π ≤ ⨆ (_ : IsValidPolicy inst π), expectedUtilityDUS inst π := by
    exact le_ciSup ⟨expectedUtilityDUS inst π, by rintro _ ⟨_, rfl⟩; exact le_rfl⟩ hπ
  have h2 : (⨆ (_ : IsValidPolicy inst π), expectedUtilityDUS inst π) ≤
      ⨆ (π' : AdaptivePolicy inst.n), ⨆ (_ : IsValidPolicy inst π'), expectedUtilityDUS inst π' := by
    exact le_ciSup hbdd π
  exact le_trans h1 h2
