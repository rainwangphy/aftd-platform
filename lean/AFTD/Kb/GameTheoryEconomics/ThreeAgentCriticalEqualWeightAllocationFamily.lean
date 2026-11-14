import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.Tcs.CriticalThreeFourBitMasksComplete
import AFTD.Kb.Tcs.CriticalThreeCanonicalDiagonalCoverage
import AFTD.Kb.Tcs.CriticalThreeSevenAllocationTablesStructure
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.Tcs.F
import AFTD.Kb.Tcs.G

/-!
# three_agent_critical_equal_weight_allocation_family

Topic: fair_division   Node: eff1d46a9dc0

Provenance: helper lemma. Constructive first-critical-family reduction for OP-1112, supported by experiments 26817 and 26821.

For three agents and seven chores, suppose each agent designates four chores high. There exist three allocations such that every chore goes once to each agent across the allocations, agent i receives three chores in round i and two in every other round, and her three-chore bundle in round i contains at most one chore she designates high.
-/

/-- Transport an allocation family along a relabelling of the chores. -/
theorem three_agent_critical_transport (H : Fin 3 → Finset (Fin 7)) (σ : Equiv.Perm (Fin 7))
    (T : Fin 3 → Fin 7 → Fin 3)
    (hbij : ∀ p, Function.Bijective (fun t => T t p))
    (hcard : ∀ t i, (Finset.univ.filter fun p => T t p = i).card = if i = t then 3 else 2)
    (hdiag : ∀ t, (Finset.univ.filter fun p => T t p = t ∧ σ p ∈ H t).card ≤ 1) :
    ∃ F : Fin 3 → Fin 7 → Fin 3, (∀ g, Function.Bijective (fun t => F t g)) ∧
      (∀ t i, (bundle_of (F t) i).card = if i = t then 3 else 2) ∧
      ∀ t, ((bundle_of (F t) t) ∩ H t).card ≤ 1 := by
  refine ⟨fun t g => T t (σ.symm g), fun g => hbij _, fun t i => ?_, fun t => ?_⟩
  · rw [← hcard t i]
    refine Finset.card_bij (fun g _ => σ.symm g) ?_ ?_ ?_
    · intro g hg
      simpa [bundle_of] using hg
    · intro a _ b _ h
      exact σ.symm.injective h
    · intro p hp
      refine ⟨σ p, ?_, by simp⟩
      simpa [bundle_of] using hp
  · refine le_trans (le_of_eq ?_) (hdiag t)
    refine Finset.card_bij (fun g _ => σ.symm g) ?_ ?_ ?_
    · intro g hg
      simpa [bundle_of] using hg
    · intro a _ b _ h
      exact σ.symm.injective h
    · intro p hp
      refine ⟨σ p, ?_, by simp⟩
      simpa [bundle_of] using hp

set_option maxRecDepth 100000 in
theorem three_agent_critical_bits (u : Fin 7 → Bool) (j : Fin 7) :
    ((if u 0 then 1 else 0) + (if u 1 then 2 else 0) + (if u 2 then 4 else 0) +
      (if u 3 then 8 else 0) + (if u 4 then 16 else 0) + (if u 5 then 32 else 0) +
      (if u 6 then 64 else 0)) / 2 ^ j.val % 2 = if u j then 1 else 0 := by
  revert u j
  decide +kernel

set_option maxRecDepth 100000 in
theorem three_agent_critical_downset (c : Fin 7 → Bool)
    (hc : ∀ p q : Fin 7, p ≤ q → c q = true → c p = true)
    (h4 : (Finset.univ.filter fun p => c p = true).card = 4) :
    ∀ p : Fin 7, c p = true ↔ p.val < 4 := by
  revert c
  decide +kernel


theorem three_agent_critical_tables : ∃ T : Fin 7 → Fin 3 → Fin 7 → Fin 3,
    (∀ k p s t, T k s p = T k t p → s = t) ∧
    (∀ k t i, (Finset.univ.filter fun p => T k t p = i).card = if i = t then 3 else 2) ∧
    (∀ k, (Finset.univ.filter fun p => T k 0 p = 0 ∧ p.val < 4).card ≤ 1) ∧
    (∀ p, (T 0 1 p = 1 ↔ p = 0 ∨ p = 1 ∨ p = 4) ∧ (T 0 2 p = 2 ↔ p = 0 ∨ p = 2 ∨ p = 3) ∧
      (T 1 1 p = 1 ↔ p = 0 ∨ p = 4 ∨ p = 5) ∧ (T 1 2 p = 2 ↔ p = 0 ∨ p = 2 ∨ p = 5) ∧
      (T 2 1 p = 1 ↔ p = 0 ∨ p = 2 ∨ p = 5) ∧ (T 2 2 p = 2 ↔ p = 1 ∨ p = 4 ∨ p = 5) ∧
      (T 3 1 p = 1 ↔ p = 1 ∨ p = 4 ∨ p = 5) ∧ (T 3 2 p = 2 ↔ p = 1 ∨ p = 4 ∨ p = 5) ∧
      (T 4 1 p = 1 ↔ p = 1 ∨ p = 2 ∨ p = 5) ∧ (T 4 2 p = 2 ↔ p = 0 ∨ p = 3 ∨ p = 5) ∧
      (T 5 1 p = 1 ↔ p = 0 ∨ p = 2 ∨ p = 4) ∧ (T 5 2 p = 2 ↔ p = 0 ∨ p = 1 ∨ p = 4) ∧
      (T 6 1 p = 1 ↔ p = 0 ∨ p = 2 ∨ p = 6) ∧ (T 6 2 p = 2 ↔ p = 0 ∨ p = 4 ∨ p = 6)) := by
  refine ⟨![
      ![![0, 2, 1, 1, 2, 0, 0], ![1, 1, 0, 0, 1, 2, 2], ![2, 0, 2, 2, 0, 1, 1]],
      ![![0, 2, 1, 1, 2, 0, 0], ![1, 0, 0, 2, 1, 1, 2], ![2, 1, 2, 0, 0, 2, 1]],
      ![![2, 1, 2, 0, 1, 0, 0], ![1, 0, 1, 2, 0, 1, 2], ![0, 2, 0, 1, 2, 2, 1]],
      ![![1, 0, 2, 1, 0, 0, 2], ![2, 1, 0, 2, 1, 1, 0], ![0, 2, 1, 0, 2, 2, 1]],
      ![![1, 2, 2, 1, 0, 0, 0], ![0, 1, 1, 0, 2, 1, 2], ![2, 0, 0, 2, 1, 2, 1]],
      ![![0, 1, 2, 2, 0, 1, 0], ![1, 0, 1, 0, 1, 2, 2], ![2, 2, 0, 1, 2, 0, 1]],
      ![![0, 2, 2, 1, 1, 0, 0], ![1, 0, 1, 2, 0, 2, 1], ![2, 1, 0, 0, 2, 1, 2]]
    ], ?_, ?_, ?_, ?_⟩
  all_goals set_option maxRecDepth 100000 in decide +kernel

theorem three_agent_critical_triple (r : Fin 7 → Fin 3) (c : Fin 3) (x y z : Fin 7)
    (hr : ∀ p, r p = c ↔ p = x ∨ p = y ∨ p = z) (hxy : x ≠ y) (hxz : x ≠ z) (hyz : y ≠ z)
    (P : Fin 7 → Prop) [DecidablePred P]
    (h : (if P x then 1 else 0) + (if P y then 1 else 0) + (if P z then 1 else 0) ≤ 1) :
    (Finset.univ.filter fun p => r p = c ∧ P p).card ≤ 1 := by
  have he : (Finset.univ.filter fun p => r p = c ∧ P p) = ({x, y, z} : Finset (Fin 7)).filter P := by
    ext p
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, hr, Finset.mem_insert,
      Finset.mem_singleton]
  rw [he, Finset.card_filter, Finset.sum_insert (by simp [hxy, hxz]),
    Finset.sum_insert (by simp [hyz]), Finset.sum_singleton]
  omega

set_option maxRecDepth 100000 in
theorem three_agent_critical_bits7 (u : Fin 7 → Bool) :
    let c := (if u 0 then 1 else 0) + (if u 1 then 2 else 0) + (if u 2 then 4 else 0) +
      (if u 3 then 8 else 0) + (if u 4 then 16 else 0) + (if u 5 then 32 else 0) +
      (if u 6 then 64 else 0)
    c < 128 ∧
    c / 2 ^ 0 % 2 = (if u 0 then 1 else 0) ∧ c / 2 ^ 1 % 2 = (if u 1 then 1 else 0) ∧
    c / 2 ^ 2 % 2 = (if u 2 then 1 else 0) ∧ c / 2 ^ 3 % 2 = (if u 3 then 1 else 0) ∧
    c / 2 ^ 4 % 2 = (if u 4 then 1 else 0) ∧ c / 2 ^ 5 % 2 = (if u 5 then 1 else 0) ∧
    c / 2 ^ 6 % 2 = (if u 6 then 1 else 0) := by
  revert u
  decide +kernel

theorem three_agent_critical_equal_weight_allocation_family (H : Fin 3 → Finset (Fin 7)) (hH : ∀ i, (H i).card = 4) : ∃ F : Fin 3 → Fin 7 → Fin 3, (∀ g, Function.Bijective (fun t => F t g)) ∧ (∀ t i, (bundle_of (F t) i).card = if i = t then 3 else 2) ∧ ∀ t, ((bundle_of (F t) t) ∩ H t).card ≤ 1 := by
  let key : Fin 7 → ℕ := fun g =>
    (if g ∈ H 0 then 0 else 4) + (if g ∈ H 1 then 1 else 0) + (if g ∈ H 2 then 2 else 0)
  set σ : Equiv.Perm (Fin 7) := Tuple.sort key with hσ
  have hmono : Monotone (key ∘ σ) := Tuple.monotone_sort _
  have hkey : ∀ p q : Fin 7, p ≤ q → key (σ p) ≤ key (σ q) := fun p q h => hmono h
  have hpre : ∀ t, (Finset.univ.filter fun p => σ p ∈ H t).card = 4 := by
    intro t
    rw [← hH t]
    refine Finset.card_bij (fun p _ => σ p) ?_ ?_ ?_
    · intro p hp; simpa using hp
    · intro a _ b _ h; exact σ.injective h
    · intro g hg
      exact ⟨σ.symm g, by simpa using hg, by simp⟩
  have hH0 : ∀ p : Fin 7, σ p ∈ H 0 ↔ p.val < 4 := by
    have hd := three_agent_critical_downset (fun p => decide (σ p ∈ H 0)) ?_ ?_
    · intro p; simpa using hd p
    · intro p q hpq hq
      have := hkey p q hpq
      simp only [decide_eq_true_eq] at hq ⊢
      by_contra hp
      simp only [key, hp, hq, if_true, if_false] at this
      split_ifs at this <;> omega
    · simpa using hpre 0
  have hpop : ∀ t, ((if σ 0 ∈ H t then 1 else 0) + (if σ 1 ∈ H t then 1 else 0) +
      (if σ 2 ∈ H t then 1 else 0) + (if σ 3 ∈ H t then 1 else 0) +
      (if σ 4 ∈ H t then 1 else 0) + (if σ 5 ∈ H t then 1 else 0) +
      (if σ 6 ∈ H t then 1 else 0)) = 4 := by
    intro t
    rw [← hpre t, Finset.card_filter, Fin.sum_univ_seven]
  have hcomplete := critical_three_four_bit_masks_complete
  have hcover := critical_three_canonical_diagonal_coverage
  dsimp only at hcomplete hcover
  obtain ⟨hc1, a0, a1, a2, a3, a4, a5, a6⟩ := three_agent_critical_bits7 (fun p => decide (σ p ∈ H 1))
  obtain ⟨hc2, b0, b1, b2, b3, b4, b5, b6⟩ := three_agent_critical_bits7 (fun p => decide (σ p ∈ H 2))
  simp only [decide_eq_true_eq] at hc1 hc2 a0 a1 a2 a3 a4 a5 a6 b0 b1 b2 b3 b4 b5 b6
  have hp1 := hpop 1
  have hp2 := hpop 2
  obtain ⟨ia, hia⟩ := hcomplete ⟨_, hc1⟩ (by
    simp only [a0, a1, a2, a3, a4, a5, a6]; omega)
  obtain ⟨ib, hib⟩ := hcomplete ⟨_, hc2⟩ (by
    simp only [b0, b1, b2, b3, b4, b5, b6]; omega)
  have hc := hcover ia ib
  simp only [hia, hib, a0, a1, a2, a3, a4, a5, a6, b0, b1, b2, b3, b4, b5, b6] at hc
  have hs : ∀ p q : Fin 7, p ≤ q → (p.val < 4 ↔ q.val < 4) →
      (if σ p ∈ H 1 then 1 else 0) + 2 * (if σ p ∈ H 2 then 1 else 0) ≤
      (if σ q ∈ H 1 then 1 else 0) + 2 * (if σ q ∈ H 2 then 1 else 0) := by
    intro p q hpq hb
    have := hkey p q hpq
    simp only [key, hH0] at this
    by_cases hp4 : p.val < 4
    · have hq4 := hb.1 hp4
      simp only [hp4, hq4, if_true] at this
      split_ifs at this ⊢ <;> omega
    · have hq4 : ¬ q.val < 4 := fun h => hp4 (hb.2 h)
      simp only [hp4, hq4, if_false] at this
      split_ifs at this ⊢ <;> omega
  have hc' := hc ⟨by omega, by omega, hs 0 1 (by decide) (by decide), hs 1 2 (by decide) (by decide),
    hs 2 3 (by decide) (by decide), hs 4 5 (by decide) (by decide), hs 5 6 (by decide) (by decide)⟩
  obtain ⟨T, hinj, hcard, h0, htri⟩ := three_agent_critical_tables
  have hbij : ∀ k p, Function.Bijective (fun t => T k t p) := fun k p =>
    Finite.injective_iff_bijective.1 (fun s t h => hinj k p s t h)
  have hd0 : ∀ k, (Finset.univ.filter fun p => T k 0 p = 0 ∧ σ p ∈ H 0).card ≤ 1 := by
    intro k
    simpa only [hH0] using h0 k
  rcases hc' with ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩ | ⟨e1, e2⟩
  · refine three_agent_critical_transport H σ (T 0) (hbij 0) (hcard 0) ?_
    intro t; fin_cases t
    · exact hd0 0
    · exact three_agent_critical_triple _ _ 0 1 4 (fun p => (htri p).1) (by decide) (by decide) (by decide) _ e1
    · exact three_agent_critical_triple _ _ 0 2 3 (fun p => (htri p).2.1) (by decide) (by decide) (by decide) _ e2
  · refine three_agent_critical_transport H σ (T 1) (hbij 1) (hcard 1) ?_
    intro t; fin_cases t
    · exact hd0 1
    · exact three_agent_critical_triple _ _ 0 4 5 (fun p => (htri p).2.2.1) (by decide) (by decide) (by decide) _ e1
    · exact three_agent_critical_triple _ _ 0 2 5 (fun p => (htri p).2.2.2.1) (by decide) (by decide) (by decide) _ e2
  · refine three_agent_critical_transport H σ (T 2) (hbij 2) (hcard 2) ?_
    intro t; fin_cases t
    · exact hd0 2
    · exact three_agent_critical_triple _ _ 0 2 5 (fun p => (htri p).2.2.2.2.1) (by decide) (by decide) (by decide) _ e1
    · exact three_agent_critical_triple _ _ 1 4 5 (fun p => (htri p).2.2.2.2.2.1) (by decide) (by decide) (by decide) _ e2
  · refine three_agent_critical_transport H σ (T 3) (hbij 3) (hcard 3) ?_
    intro t; fin_cases t
    · exact hd0 3
    · exact three_agent_critical_triple _ _ 1 4 5 (fun p => (htri p).2.2.2.2.2.2.1) (by decide) (by decide) (by decide) _ e1
    · exact three_agent_critical_triple _ _ 1 4 5 (fun p => (htri p).2.2.2.2.2.2.2.1) (by decide) (by decide) (by decide) _ e2
  · refine three_agent_critical_transport H σ (T 4) (hbij 4) (hcard 4) ?_
    intro t; fin_cases t
    · exact hd0 4
    · exact three_agent_critical_triple _ _ 1 2 5 (fun p => (htri p).2.2.2.2.2.2.2.2.1) (by decide) (by decide) (by decide) _ e1
    · exact three_agent_critical_triple _ _ 0 3 5 (fun p => (htri p).2.2.2.2.2.2.2.2.2.1) (by decide) (by decide) (by decide) _ e2
  · refine three_agent_critical_transport H σ (T 5) (hbij 5) (hcard 5) ?_
    intro t; fin_cases t
    · exact hd0 5
    · exact three_agent_critical_triple _ _ 0 2 4 (fun p => (htri p).2.2.2.2.2.2.2.2.2.2.1) (by decide) (by decide) (by decide) _ e1
    · exact three_agent_critical_triple _ _ 0 1 4 (fun p => (htri p).2.2.2.2.2.2.2.2.2.2.2.1) (by decide) (by decide) (by decide) _ e2
  · refine three_agent_critical_transport H σ (T 6) (hbij 6) (hcard 6) ?_
    intro t; fin_cases t
    · exact hd0 6
    · exact three_agent_critical_triple _ _ 0 2 6 (fun p => (htri p).2.2.2.2.2.2.2.2.2.2.2.2.1) (by decide) (by decide) (by decide) _ e1
    · exact three_agent_critical_triple _ _ 0 4 6 (fun p => (htri p).2.2.2.2.2.2.2.2.2.2.2.2.2) (by decide) (by decide) (by decide) _ e2
