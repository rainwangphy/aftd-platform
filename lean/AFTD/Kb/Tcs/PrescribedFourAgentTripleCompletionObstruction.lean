import AFTD.Prelude

/-!
# prescribed_four_agent_triple_completion_obstruction

Topic: combinatorics   Node: e300735ce63c

Provenance: helper lemma. An explicit obstruction to a proposed allocation-completion criterion, experiment 26849.

There is no four-round assignment of nine chores to four agents in which each chore visits each agent once, round i gives agent i three chores and every other agent two chores, and chores 0, 1 and 2 go to agent 0 in round 0, agent 1 in round 1, and an agent other than 2 in round 2.
-/

theorem prescribed_four_agent_triple_completion_obstruction :
    ¬ ∃ F : Fin 4 → Fin 9 → Fin 4,
      (∀ g, Function.Bijective (fun t => F t g)) ∧
      (∀ t i, (Finset.univ.filter fun g => F t g = i).card = if i = t then 3 else 2) ∧
      ∀ g ∈ ({0,1,2} : Finset (Fin 9)), F 0 g = 0 ∧ F 1 g = 1 ∧ F 2 g ≠ 2 := by
  classical
  rintro ⟨F, hbij, hsize, hfixed⟩
  have hmust (g : Fin 9) (hg : g ∈ ({0,1,2} : Finset (Fin 9))) : F 2 g = 3 := by
    obtain ⟨ha, hb, hc⟩ := hfixed g hg
    have hzero : F 2 g ≠ 0 := by
      intro he
      have heq : (2 : Fin 4) = 0 := (hbij g).1 (he.trans ha.symm)
      exact (by decide : (2 : Fin 4) ≠ 0) heq
    have hone : F 2 g ≠ 1 := by
      intro he
      have heq : (2 : Fin 4) = 1 := (hbij g).1 (he.trans hb.symm)
      exact (by decide : (2 : Fin 4) ≠ 1) heq
    generalize he : F 2 g = x
    fin_cases x <;> simp_all
  have hsubset : ({0,1,2} : Finset (Fin 9)) ⊆ Finset.univ.filter (fun g => F 2 g = 3) := by
    intro g hg
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    exact hmust g hg
  have hcard := Finset.card_le_card hsubset
  have hthree : ({0,1,2} : Finset (Fin 9)).card = 3 := by decide
  have htwo : (Finset.univ.filter fun g : Fin 9 => F 2 g = 3).card = 2 := by
    simpa using hsize 2 3
  rw [hthree, htwo] at hcard
  exact (by decide : ¬ 3 ≤ 2) hcard
