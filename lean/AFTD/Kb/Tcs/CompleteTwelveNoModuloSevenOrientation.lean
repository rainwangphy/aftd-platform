import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphHasModuloOrientation

/-!
# complete_twelve_no_modulo_seven_orientation

Topic: graphs   Node: cd22edea25fa

Provenance: formalization of a published result. Source: arXiv:2610.07034 Prop. 6.2

The complete graph on 12 vertices does not have a modulo-7 orientation.
-/

/-- The complete graph on 12 vertices has no modulo-7 orientation. -/
theorem complete_twelve_no_modulo_seven_orientation :
    ¬ simple_graph_has_modulo_orientation (SimpleGraph.completeGraph (Fin 12)) 7 := by
  classical
  rintro ⟨R, ⟨hadj, horient⟩, hbal⟩
  -- Every vertex has outdegree + indegree = 11.
  have hdeg : ∀ v : Fin 12, (Finset.univ.filter (fun w => R v w)).card + (Finset.univ.filter (fun w => R w v)).card = 11 := by
    intro v
    rw [Finset.card_filter, Finset.card_filter, ← Finset.sum_add_distrib]
    have hterm : ∀ w : Fin 12, (if R v w then (1:ℕ) else 0) + (if R w v then 1 else 0) = if w = v then 0 else 1 := by
      intro w
      by_cases hwv : w = v
      · rw [← hwv]
        have hnv : ¬ R w w := by
          intro h; have := hadj w w h; simp at this
        simp [hnv]
      · have hadjvw : (SimpleGraph.completeGraph (Fin 12)).Adj v w := fun h => hwv h.symm
        rcases horient v w hadjvw with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp [h1, h2, hwv]
        · simp [h1, h2, hwv]
    rw [Finset.sum_congr rfl (fun w _ => hterm w)]
    have h1 : (∑ w : Fin 12, if w = v then (0:ℕ) else 1) = ∑ w : Fin 12, if w ≠ v then (1:ℕ) else 0 := by
      apply Finset.sum_congr rfl
      intro w _
      by_cases h : w = v <;> simp [h]
    rw [h1, ← Finset.card_filter (fun w : Fin 12 => w ≠ v), Finset.filter_ne']
    simp
  -- Every outdegree is 2 or 9.
  have hval : ∀ v : Fin 12, (Finset.univ.filter (fun w => R v w)).card = 2 ∨ (Finset.univ.filter (fun w => R v w)).card = 9 := by
    intro v
    have hle : (Finset.univ.filter (fun w => R v w)).card ≤ 11 := by have := hdeg v; omega
    have hi : (Finset.univ.filter (fun w => R w v)).card = 11 - (Finset.univ.filter (fun w => R v w)).card := by
      have := hdeg v; omega
    have h2 : (2 * ((Finset.univ.filter (fun w => R v w)).card : ZMod 7) : ZMod 7) = 11 := by
      have h := hbal v
      rw [hi] at h
      have hcast : ((11 - (Finset.univ.filter (fun w => R v w)).card : ℕ) : ZMod 7)
          = (11 : ZMod 7) - ((Finset.univ.filter (fun w => R v w)).card : ZMod 7) := by
        rw [Nat.cast_sub hle]; push_cast; ring
      rw [hcast] at h
      rw [eq_sub_iff_add_eq] at h
      rw [two_mul]
      exact h
    have h2n : ((2 * (Finset.univ.filter (fun w => R v w)).card : ℕ) : ZMod 7) = ((11 : ℕ) : ZMod 7) := by
      push_cast
      exact h2
    have hmod : (2 * (Finset.univ.filter (fun w => R v w)).card) % 7 = 4 := by
      have := (ZMod.natCast_eq_natCast_iff' (2 * (Finset.univ.filter (fun w => R v w)).card) 11 7).mp h2n
      simpa using this
    omega
  -- The sum of all outdegrees is 66.
  have hsum : (∑ v : Fin 12, (Finset.univ.filter (fun w => R v w)).card) = 66 := by
    have hsym : (∑ v : Fin 12, (Finset.univ.filter (fun w => R v w)).card)
              = (∑ v : Fin 12, (Finset.univ.filter (fun w => R w v)).card) := by
      simp only [Finset.card_filter]
      rw [Finset.sum_comm]
    have htot : (∑ v : Fin 12, ((Finset.univ.filter (fun w => R v w)).card + (Finset.univ.filter (fun w => R w v)).card)) = 132 := by
      rw [Finset.sum_congr rfl (fun v _ => hdeg v)]
      simp
    rw [Finset.sum_add_distrib] at htot
    rw [← hsym] at htot
    omega
  -- Six vertices have outdegree 2.
  set S : Finset (Fin 12) := Finset.univ.filter (fun v => (Finset.univ.filter (fun w => R v w)).card = 2) with hSdef
  have hScard : S.card = 6 := by
    have hSle : S.card ≤ 12 := by
      have := Finset.card_le_univ S
      simpa using this
    have h1 : (∑ v : Fin 12, (Finset.univ.filter (fun w => R v w)).card)
            = ∑ v : Fin 12, (if (Finset.univ.filter (fun w => R v w)).card = 2 then (2:ℕ) else 9) := by
      apply Finset.sum_congr rfl
      intro v _
      rcases hval v with h | h <;> simp [h]
    have hc : (Finset.univ.filter (fun v => ¬ (Finset.univ.filter (fun w => R v w)).card = 2)).card = 12 - S.card := by
      have hthis := Finset.card_filter_add_card_filter_not (s := Finset.univ) (p := fun v : Fin 12 => (Finset.univ.filter (fun w => R v w)).card = 2)
      simp only [Finset.card_univ, Fintype.card_fin] at hthis
      rw [← hSdef] at hthis
      omega
    have h2 : (∑ v : Fin 12, (if (Finset.univ.filter (fun w => R v w)).card = 2 then (2:ℕ) else 9))
            = 2 * S.card + 9 * (12 - S.card) := by
      rw [Finset.sum_ite]
      rw [Finset.sum_const_nat (m := 2) (fun v _ => rfl), Finset.sum_const_nat (m := 9) (fun v _ => rfl)]
      rw [← hSdef]
      rw [hc]
      omega
    have h3 : 2 * S.card + 9 * (12 - S.card) = 66 := by
      rw [← h2, ← h1]; exact hsum
    show S.card = 6
    omega
  -- Double counting: internal edges of S.
  have h2sum : 2 * (∑ v ∈ S, (S.filter (fun w => R v w)).card) = S.card * (S.card - 1) := by
    have hpair : ∀ v w : Fin 12, (if R v w then (1:ℕ) else 0) + (if R w v then (1:ℕ) else 0) = if v = w then 0 else 1 := by
      intro v w
      by_cases h : v = w
      · rw [h]
        have hnv : ¬ R w w := by
          intro hr; have := hadj w w hr; simp at this
        simp [hnv]
      · have hadjvw : (SimpleGraph.completeGraph (Fin 12)).Adj v w := fun hr => h hr
        rcases horient v w hadjvw with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · simp [h1, h2, h]
        · simp [h1, h2, h]
    have hT_eq : (∑ v ∈ S, (S.filter (fun w => R v w)).card) = ∑ v ∈ S, ∑ w ∈ S, (if R v w then (1:ℕ) else 0) := by
      apply Finset.sum_congr rfl
      intro v _
      rw [Finset.card_filter]
    have hsym : (∑ v ∈ S, ∑ w ∈ S, (if R v w then (1:ℕ) else 0)) = (∑ v ∈ S, ∑ w ∈ S, (if R w v then (1:ℕ) else 0)) := by
      rw [Finset.sum_comm]
    have h2T : 2 * (∑ v ∈ S, ∑ w ∈ S, (if R v w then (1:ℕ) else 0))
              = ∑ v ∈ S, ∑ w ∈ S, ((if R v w then (1:ℕ) else 0) + (if R w v then (1:ℕ) else 0)) := by
      rw [two_mul]
      nth_rewrite 2 [hsym]
      simp only [Finset.sum_add_distrib]
    have hpost : (∑ v ∈ S, ∑ w ∈ S, ((if R v w then (1:ℕ) else 0) + (if R w v then (1:ℕ) else 0)))
               = ∑ v ∈ S, ∑ w ∈ S, (if v = w then (0:ℕ) else 1) := by
      apply Finset.sum_congr rfl
      intro v _
      apply Finset.sum_congr rfl
      intro w _
      exact hpair v w
    have hinner : ∀ v ∈ S, (∑ w ∈ S, (if v = w then (0:ℕ) else 1)) = S.card - 1 := by
      intro v hv
      have h1 : (∑ w ∈ S, (if v = w then (0:ℕ) else 1)) = ∑ w ∈ S, (if v ≠ w then (1:ℕ) else 0) := by
        apply Finset.sum_congr rfl
        intro w _
        by_cases h : v = w <;> simp [h]
      rw [h1, ← Finset.card_filter (fun w : Fin 12 => v ≠ w), Finset.filter_ne, Finset.card_erase_of_mem hv]
    have hfinal : (∑ v ∈ S, ∑ w ∈ S, (if v = w then (0:ℕ) else 1)) = S.card * (S.card - 1) := by
      rw [Finset.sum_congr rfl (fun v hv => hinner v hv)]
      exact Finset.sum_const_nat (fun v _ => rfl)
    rw [hT_eq, h2T, hpost, hfinal]
  -- Each internal outdegree is at most the total outdegree = 2 on S.
  have hle : (∑ v ∈ S, (S.filter (fun w => R v w)).card) ≤ ∑ v ∈ S, (Finset.univ.filter (fun w => R v w)).card := by
    apply Finset.sum_le_sum
    intro v hv
    apply Finset.card_le_card
    exact Finset.filter_subset_filter _ (Finset.subset_univ _)
  have hout : (∑ v ∈ S, (Finset.univ.filter (fun w => R v w)).card) = S.card * 2 := by
    have h : ∀ v ∈ S, (Finset.univ.filter (fun w => R v w)).card = 2 := by
      intro v hv
      exact (Finset.mem_filter.mp hv).2
    rw [Finset.sum_congr rfl h]
    exact Finset.sum_const_nat (fun v _ => rfl)
  rw [hScard] at h2sum hout
  rw [hout] at hle
  omega
