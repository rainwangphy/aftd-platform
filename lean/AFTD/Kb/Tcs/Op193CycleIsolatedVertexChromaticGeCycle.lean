import AFTD.Prelude
import AFTD.Kb.Tcs.GStableKneser
import AFTD.Kb.Tcs.Op193KneserHomSumInl

/-!
# op_193_cycle_isolated_vertex_chromatic_ge_cycle

Topic: graphs   Node: 15cf11a8291e

Provenance: helper lemma. arXiv:2610.17884 Sec. 1 -- The chromatic number of G-stable Kneser graphs

For any natural numbers k and m, the chromatic number of the G-stable Kneser graph of the disjoint union of an m-cycle and an isolated vertex is at least the chromatic number of the G-stable Kneser graph of the m-cycle.
-/

/-- The chromatic number of KG(C_m ⊔ K_1, k) is at least the chromatic number of KG(C_m, k). -/
theorem op_193_cycle_isolated_vertex_chromatic_ge_cycle (k m : ℕ) :
    (GStableKneser (SimpleGraph.cycleGraph m) k).chromaticNumber ≤
      (GStableKneser ((SimpleGraph.cycleGraph m).sum (⊥ : SimpleGraph Unit)) k).chromaticNumber := by
  obtain ⟨f⟩ := op_193_kneser_hom_sum_inl (SimpleGraph.cycleGraph m) (⊥ : SimpleGraph Unit) k
  exact SimpleGraph.chromaticNumber_mono_of_hom f
