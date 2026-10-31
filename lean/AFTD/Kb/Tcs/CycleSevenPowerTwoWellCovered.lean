import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsWellCovered
import AFTD.Kb.Tcs.SimpleGraphPower

/-!
# cycle_seven_power_two_well_covered

Topic: graphs   Node: c9863b2be288

Provenance: helper lemma. step towards cycle_seven_all_powers_well_covered

The square of the 7-cycle graph is well-covered: all maximal independent sets have size 2.
-/

open SimpleGraph

private theorem cycle_seven_power_two_well_covered_edist_le_two_iff {V : Type*} (G : SimpleGraph V) (u v : V) :
    G.edist u v ≤ (2 : ℕ∞) ↔ u = v ∨ G.Adj u v ∨ (G.commonNeighbors u v).Nonempty := by
  rw [← not_iff_not]
  push Not
  exact SimpleGraph.two_lt_edist_iff

private def cycle_seven_power_two_well_covered_G : SimpleGraph (Fin 7) where
  Adj u v := u ≠ v ∧ ((cycleGraph 7).Adj u v ∨ ∃ w : Fin 7, (cycleGraph 7).Adj u w ∧ (cycleGraph 7).Adj w v)
  symm := ⟨by
    intro u v ⟨hne, h⟩
    refine ⟨hne.symm, ?_⟩
    rcases h with h1 | ⟨w, hw1, hw2⟩
    · left; exact h1.symm
    · right; exact ⟨w, hw2.symm, hw1.symm⟩⟩
  loopless := ⟨fun u ⟨hne, _⟩ => hne rfl⟩

private lemma cycle_seven_power_two_well_covered_eq :
    simple_graph_power (cycleGraph 7) 2 = cycle_seven_power_two_well_covered_G := by
  ext u v
  simp only [simple_graph_power, cycle_seven_power_two_well_covered_G, Nat.cast_ofNat]
  rw [cycle_seven_power_two_well_covered_edist_le_two_iff]
  simp only [mem_commonNeighbors, Set.Nonempty]
  constructor
  · rintro ⟨hne, rfl | hadj | ⟨w, hw1, hw2⟩⟩
    · exact (hne rfl).elim
    · exact ⟨hne, Or.inl hadj⟩
    · exact ⟨hne, Or.inr ⟨w, hw1, hw2.symm⟩⟩
  · rintro ⟨hne, hadj | ⟨w, hw1, hw2⟩⟩
    · exact ⟨hne, Or.inr (Or.inl hadj)⟩
    · exact ⟨hne, Or.inr (Or.inr ⟨w, hw1, hw2.symm⟩)⟩

instance cycle_seven_power_two_well_covered_decidableRel :
    DecidableRel cycle_seven_power_two_well_covered_G.Adj := by
  intro u v
  dsimp [cycle_seven_power_two_well_covered_G]
  infer_instance

/-- The square of the 7-cycle graph is well-covered: all maximal independent sets have size 2. -/
theorem cycle_seven_power_two_well_covered :
    simple_graph_is_well_covered (simple_graph_power (SimpleGraph.cycleGraph 7) 2) := by
  rw [cycle_seven_power_two_well_covered_eq]
  unfold simple_graph_is_well_covered
  simp only [Maximal]
  decide
