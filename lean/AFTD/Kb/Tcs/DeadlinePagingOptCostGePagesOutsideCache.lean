import AFTD.Prelude
import AFTD.Kb.Tcs.IsFeasibleSchedule
import AFTD.Kb.Tcs.ScheduleCost
import AFTD.Kb.Tcs.InstanceHorizon
import AFTD.Kb.Tcs.DeadlineRequest

/-!
# deadline_paging_opt_cost_ge_pages_outside_cache

Topic: online_algorithms   Node: 922c8cea7c53

Provenance: helper lemma. step towards deadline_paging_optimal_competitive_ratio_two_holes

Every feasible schedule must fetch each requested page outside the initial cache at least once, so its fetch cost is at least the number of distinct requested pages outside C₀.
-/

lemma deadline_paging_opt_cost_ge_pages_outside_cache_deadline_lt_instanceHorizon
    {α : Type*} {reqs : List (DeadlineRequest α)} {r : DeadlineRequest α} (hr : r ∈ reqs) :
    r.deadline < instanceHorizon reqs := by
  induction reqs with
  | nil => contradiction
  | cons hd tl ih =>
    simp only [instanceHorizon, List.foldr_cons]
    rcases List.mem_cons.mp hr with rfl | htl
    · have : r.deadline + 1 ≤ max (r.deadline + 1) (List.foldr (fun r m => max (r.deadline + 1) m) 0 tl) :=
        le_max_left _ _
      exact Nat.lt_of_lt_of_le (Nat.lt_succ_self _) this
    · have ih' := ih htl
      have : List.foldr (fun r m => max (r.deadline + 1) m) 0 tl ≤
        max (hd.deadline + 1) (List.foldr (fun r m => max (r.deadline + 1) m) 0 tl) :=
        le_max_right _ _
      exact Nat.lt_of_lt_of_le ih' this

/-- The fetch cost of any feasible schedule is at least the number of distinct requested pages outside the initial cache. -/
theorem deadline_paging_opt_cost_ge_pages_outside_cache
    {α : Type*} [DecidableEq α] (k : ℕ) (C₀ : Finset α)
    (sched : ℕ → Finset α) (reqs : List (DeadlineRequest α))
    (h : IsFeasibleSchedule k C₀ sched reqs) :
    ((reqs.map (fun r => r.page)).toFinset \ C₀).card ≤ scheduleCost sched (instanceHorizon reqs) := by
  classical
  let s := (reqs.map (fun r => r.page)).toFinset \ C₀
  let f : α → ℕ := fun p =>
    if hex : ∃ t, p ∈ sched t then Nat.find hex - 1 else 0
  have h_maps : Set.MapsTo f ↑s ↑(Finset.range (instanceHorizon reqs)) := by
    intro p hp
    rw [Finset.mem_coe, Finset.mem_sdiff, List.mem_toFinset, List.mem_map] at hp
    rcases hp with ⟨⟨r, hr, rfl⟩, hpC0⟩
    rcases h.2.2 r hr with ⟨t, ht_arr, ht_dead, ht_mem⟩
    have hex : ∃ t, r.page ∈ sched t := ⟨t, ht_mem⟩
    simp only [Finset.mem_coe, Finset.mem_range]
    dsimp [f]
    rw [dif_pos hex]
    have hfind_le : Nat.find hex ≤ t := Nat.find_min' hex ht_mem
    have hdead := deadline_paging_opt_cost_ge_pages_outside_cache_deadline_lt_instanceHorizon hr
    have : Nat.find hex - 1 ≤ Nat.find hex := Nat.sub_le _ _
    exact lt_of_le_of_lt (le_trans this (le_trans hfind_le ht_dead)) hdead
  rw [Finset.card_eq_sum_card_fiberwise h_maps]
  unfold scheduleCost
  apply Finset.sum_le_sum
  intro b hb
  apply Finset.card_le_card
  intro p hp
  simp only [Finset.mem_filter] at hp
  rcases hp with ⟨hps, hfp⟩
  have hp_sdiff := hps
  rw [Finset.mem_sdiff, List.mem_toFinset, List.mem_map] at hp_sdiff
  rcases hp_sdiff with ⟨⟨r, hr, rfl⟩, hpC0⟩
  rcases h.2.2 r hr with ⟨t, ht_arr, ht_dead, ht_mem⟩
  have hex : ∃ t, r.page ∈ sched t := ⟨t, ht_mem⟩
  dsimp [f] at hfp
  rw [dif_pos hex] at hfp
  have hpos : Nat.find hex ≠ 0 := by
    intro hzero
    have hspec := Nat.find_spec hex
    rw [hzero, h.1] at hspec
    exact hpC0 hspec
  have heq : Nat.find hex = b + 1 := by
    omega
  rw [Finset.mem_sdiff]
  constructor
  · have hspec := Nat.find_spec hex
    rwa [heq] at hspec
  · intro hbad
    have hlt : b < Nat.find hex := by omega
    exact Nat.find_min hex hlt hbad
