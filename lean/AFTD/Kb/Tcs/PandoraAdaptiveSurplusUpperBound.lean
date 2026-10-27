import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.DiscreteDist
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.IsValidPolicy
import AFTD.Kb.Tcs.IsPartiallyAdaptive
import AFTD.Kb.Tcs.ExpectedUtilityDUS
import AFTD.Kb.Tcs.PandoraIsReservation
import AFTD.Kb.Tcs.PandoraCappedSurplus
import AFTD.Kb.Tcs.PandoraDeadlineFeasible
import AFTD.Kb.Tcs.IsValidPolicyAux
import AFTD.Kb.Tcs.Support

/-!
# pandora_adaptive_surplus_upper_bound

Topic: online_algorithms   Node: a72bc3fc5bfe

Provenance: helper lemma. Helper for op184_partially_adaptive_half_approximation: arXiv:2610.13775 Section 3, Lemma 1 (adaptive-surplus upper bound)

Lemma 1: for reservation values r and any threshold t >= 0, every valid adaptive policy has expected DUS utility at most t plus the total capped surplus of some deadline-feasible set.
-/

/-- Expected total capped surplus of the boxes a policy opens. -/
noncomputable def pandora_adaptive_surplus_upper_bound_opened (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (t : ℝ) : AdaptivePolicy inst.n → ℝ
  | .stop => 0
  | .openBox b cont => pandora_capped_surplus inst r b t +
      ∑ v ∈ (inst.dist b).support,
        (inst.dist b).prob v * pandora_adaptive_surplus_upper_bound_opened inst r t (cont v)

theorem pandora_adaptive_surplus_upper_bound_foldl {α : Type*} (A : ℝ) :
    ∀ (h : List (α × ℝ)) (acc : ℝ), acc ≤ A → (∀ bv ∈ h, bv.2 ≤ A) →
      h.foldl (fun acc bv => max acc bv.2) acc ≤ A := by
  intro h
  induction h with
  | nil => intro acc hacc _; simpa using hacc
  | cons a h ih =>
    intro acc hacc hall
    simp only [List.foldl_cons]
    exact ih _ (max_le hacc (hall a (by simp))) (fun bv hbv => hall bv (by simp [hbv]))

theorem pandora_adaptive_surplus_upper_bound_utility (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (hr : pandora_is_reservation inst r) (t : ℝ) (ht : 0 ≤ t) :
    ∀ (π : AdaptivePolicy inst.n) (hist : List (Fin inst.n × ℝ)),
      expectedUtilityDUS.aux inst hist π ≤ t +
        (hist.map (fun bv => max (min bv.2 (r bv.1) - t) 0 + max (bv.2 - r bv.1) 0)).sum +
        pandora_adaptive_surplus_upper_bound_opened inst r t π := by
  intro π
  induction π with
  | stop =>
    intro hist
    simp only [expectedUtilityDUS.aux, pandora_adaptive_surplus_upper_bound_opened, add_zero]
    have hnn : ∀ x ∈ hist.map (fun bv => max (min bv.2 (r bv.1) - t) 0 + max (bv.2 - r bv.1) 0),
        0 ≤ x := by
      intro x hx
      simp only [List.mem_map] at hx
      obtain ⟨bv, -, rfl⟩ := hx
      exact add_nonneg (le_max_right _ _) (le_max_right _ _)
    apply pandora_adaptive_surplus_upper_bound_foldl
    · have := List.sum_nonneg hnn
      linarith
    · intro bv hbv
      have h1 := List.single_le_sum hnn _ (List.mem_map.2 ⟨bv, hbv, rfl⟩)
      have h2 : bv.2 ≤ t + (max (min bv.2 (r bv.1) - t) 0 + max (bv.2 - r bv.1) 0) := by
        rcases le_total bv.2 (r bv.1) with h | h
        · rw [min_eq_left h]
          have := le_max_left (bv.2 - t) 0
          have := le_max_right (bv.2 - r bv.1) 0
          linarith
        · rw [min_eq_right h]
          have := le_max_left (r bv.1 - t) 0
          have := le_max_left (bv.2 - r bv.1) 0
          linarith
      linarith
  | openBox b cont ih =>
    intro hist
    simp only [expectedUtilityDUS.aux, pandora_adaptive_surplus_upper_bound_opened]
    have hle : ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v * expectedUtilityDUS.aux inst ((b, v) :: hist) (cont v) ≤
        ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v * (t +
          (hist.map (fun bv => max (min bv.2 (r bv.1) - t) 0 + max (bv.2 - r bv.1) 0)).sum +
          (max (min v (r b) - t) 0 + max (v - r b) 0) +
          pandora_adaptive_surplus_upper_bound_opened inst r t (cont v)) := by
      apply Finset.sum_le_sum
      intro v hv
      apply mul_le_mul_of_nonneg_left _ ((inst.dist b).prob_nonneg v hv)
      have := ih v ((b, v) :: hist)
      simp only [List.map_cons, List.sum_cons] at this
      linarith
    have hsum : ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v * (t +
          (hist.map (fun bv => max (min bv.2 (r bv.1) - t) 0 + max (bv.2 - r bv.1) 0)).sum +
          (max (min v (r b) - t) 0 + max (v - r b) 0) +
          pandora_adaptive_surplus_upper_bound_opened inst r t (cont v)) =
        (t + (hist.map (fun bv => max (min bv.2 (r bv.1) - t) 0 + max (bv.2 - r bv.1) 0)).sum) *
            ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v +
          pandora_capped_surplus inst r b t + inst.cost b +
          ∑ v ∈ (inst.dist b).support, (inst.dist b).prob v * pandora_adaptive_surplus_upper_bound_opened inst r t (cont v) := by
      rw [← hr b]
      simp only [pandora_capped_surplus, Finset.mul_sum]
      rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl (fun v _ => ?_)
      ring
    rw [(inst.dist b).sum_prob_one] at hsum
    linarith

theorem pandora_adaptive_surplus_upper_bound_path (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (t : ℝ) :
    ∀ (π : AdaptivePolicy inst.n) (O : List (Fin inst.n)), IsValidPolicyAux inst rfl O π →
      ∃ S : Finset (Fin inst.n), (∀ i ∈ S, i ∉ O) ∧
        (∀ j : ℕ, (S.filter (fun i => inst.deadline i ≤ j)).card ≤ j - O.length) ∧
        pandora_adaptive_surplus_upper_bound_opened inst r t π ≤
          ∑ i ∈ S, pandora_capped_surplus inst r i t := by
  intro π
  induction π with
  | stop =>
    intro O _
    exact ⟨∅, by simp, by simp, by simp [pandora_adaptive_surplus_upper_bound_opened]⟩
  | openBox b cont ih =>
    intro O hv
    obtain ⟨hbO, hdl, hcont⟩ := hv
    have hdl' : O.length + 1 ≤ inst.deadline b := hdl
    set D := inst.dist b
    have hne : D.support.Nonempty := by
      rw [Finset.nonempty_iff_ne_empty]
      intro he
      have := D.sum_prob_one
      rw [he, Finset.sum_empty] at this
      norm_num at this
    obtain ⟨v0, hv0, hmax⟩ := Finset.exists_max_image D.support
      (fun v => pandora_adaptive_surplus_upper_bound_opened inst r t (cont v)) hne
    obtain ⟨S, hSO, hSf, hSW⟩ := ih v0 (b :: O) (hcont v0 hv0)
    have hbS : b ∉ S := fun h => hSO b h (by simp)
    refine ⟨insert b S, ?_, ?_, ?_⟩
    · intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · exact hbO
      · exact fun h => hSO i hi (List.mem_cons_of_mem _ h)
    · intro j
      have h1 := hSf j
      simp only [List.length_cons] at h1
      rw [Finset.filter_insert]
      split_ifs with hb
      · have := Finset.card_insert_le b (S.filter (fun i => inst.deadline i ≤ j))
        omega
      · omega
    · simp only [pandora_adaptive_surplus_upper_bound_opened]
      rw [Finset.sum_insert hbS]
      have : ∑ v ∈ D.support, D.prob v *
            pandora_adaptive_surplus_upper_bound_opened inst r t (cont v) ≤
          ∑ v ∈ D.support, D.prob v *
            pandora_adaptive_surplus_upper_bound_opened inst r t (cont v0) :=
        Finset.sum_le_sum (fun v hv => mul_le_mul_of_nonneg_left (hmax v hv) (D.prob_nonneg v hv))
      rw [← Finset.sum_mul, D.sum_prob_one, one_mul] at this
      linarith

theorem pandora_adaptive_surplus_upper_bound (inst : PandoraDeadlineInstance)
    (r : Fin inst.n → ℝ) (hr : pandora_is_reservation inst r) (t : ℝ) (ht : 0 ≤ t)
    (π : AdaptivePolicy inst.n) (hπ : IsValidPolicy inst π) :
    ∃ S : Finset (Fin inst.n), pandora_deadline_feasible inst S ∧
      expectedUtilityDUS inst π ≤ t + ∑ i ∈ S, pandora_capped_surplus inst r i t := by
  obtain ⟨S, -, hSf, hSW⟩ := pandora_adaptive_surplus_upper_bound_path inst r t π [] hπ
  refine ⟨S, fun j => by simpa using hSf j, ?_⟩
  have := pandora_adaptive_surplus_upper_bound_utility inst r hr t ht π []
  simp only [List.map_nil, List.sum_nil, add_zero] at this
  unfold expectedUtilityDUS
  linarith
