import AFTD.Prelude
import AFTD.Kb.Tcs.IsFeasibleSchedule
import AFTD.Kb.Tcs.DeadlineRequest

/-!
# deadline_paging_feasible_iff_exists_service_time

Topic: online_algorithms   Node: bff156b32368

Provenance: helper lemma. step towards deadline_paging_optimal_competitive_ratio_two_holes

An instance is feasible iff one can assign every request a service time inside its window so that each non-zero time slot sees at most k distinct pages and slot 0 sees only pages of the initial cache C₀.
-/

/-- Feasibility is equivalent to an assignment of service times with a per-slot capacity condition (≤ k distinct pages off slot 0, only C₀ at slot 0); caching is a cost matter, never a feasibility blocker. -/
theorem deadline_paging_feasible_iff_exists_service_time
    {α : Type*} [DecidableEq α] (k : ℕ) (C₀ : Finset α) (hC₀ : C₀.card = k)
    (reqs : List (DeadlineRequest α)) :
    (∃ sched : ℕ → Finset α, IsFeasibleSchedule k C₀ sched reqs) ↔
      ∃ f : Fin reqs.length → ℕ,
        (∀ i, (reqs.get i).arrival ≤ f i ∧ f i ≤ (reqs.get i).deadline) ∧
        (∀ t, t ≠ 0 →
          ((Finset.univ.filter (fun i => f i = t)).image (fun i => (reqs.get i).page)).card ≤ k) ∧
        ((Finset.univ.filter (fun i => f i = 0)).image (fun i => (reqs.get i).page)) ⊆ C₀ := by
  constructor
  · rintro ⟨sched, hsched⟩
    rcases hsched with ⟨h0, hcard, hserve⟩
    have h_each : ∀ i : Fin reqs.length, ∃ t, (reqs.get i).arrival ≤ t ∧ t ≤ (reqs.get i).deadline ∧ (reqs.get i).page ∈ sched t := by
      intro i
      exact hserve (reqs.get i) (List.get_mem reqs i)
    choose f hf using h_each
    refine ⟨f, ?_, ?_, ?_⟩
    · intro i
      exact ⟨(hf i).1, (hf i).2.1⟩
    · intro t ht
      have hsub : ((Finset.univ.filter (fun i => f i = t)).image (fun i => (reqs.get i).page)) ⊆ sched t := by
        intro p hp
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hp
        rcases hp with ⟨i, hi, rfl⟩
        have := (hf i).2.2
        rw [hi] at this
        exact this
      exact le_trans (Finset.card_le_card hsub) (hcard t)
    · intro p hp
      simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and] at hp
      rcases hp with ⟨i, hi, rfl⟩
      have := (hf i).2.2
      rw [hi, h0] at this
      exact this
  · rintro ⟨f, hwin, hcap, hC0_sub⟩
    let sched : ℕ → Finset α := fun t =>
      if t = 0 then C₀ else ((Finset.univ.filter (fun i => f i = t)).image (fun i => (reqs.get i).page))
    refine ⟨sched, ?_, ?_, ?_⟩
    · show sched 0 = C₀
      dsimp [sched]
    · intro t
      dsimp [sched]
      split_ifs with ht
      · rw [hC₀]
      · exact hcap t ht
    · intro r hr
      rcases List.mem_iff_get.mp hr with ⟨i, rfl⟩
      refine ⟨f i, (hwin i).1, (hwin i).2, ?_⟩
      dsimp [sched]
      split_ifs with ht
      · apply hC0_sub
        simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨i, ht, rfl⟩
      · simp only [Finset.mem_image, Finset.mem_filter, Finset.mem_univ, true_and]
        exact ⟨i, rfl, rfl⟩
