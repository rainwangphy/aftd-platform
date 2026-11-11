import AFTD.Prelude
import AFTD.Kb.Tcs.Op869GraphFromPredecessors

/-!
# op869_predecessor_colorable_iff

Topic: online_algorithms   Node: 2b8eadea9799

Provenance: helper lemma. arXiv:2610.41516, Sections 1 and 2; formal infrastructure for the adaptive online-coloring construction.

The graph built from predecessor sets is k-colorable exactly when the vertices admit k colors with different colors on each earlier-neighbor incidence.
-/

theorem op869_predecessor_colorable_iff {n k : ℕ} (P : Fin n → Finset (Fin n)) :
    (op869_graph_from_predecessors P).Colorable k ↔
      ∃ c : Fin n → Fin k, ∀ i j : Fin n, i < j → i ∈ P j → c i ≠ c j := by
  constructor
  · rintro ⟨c⟩
    refine ⟨c, ?_⟩
    intro i j hij hmem
    exact c.valid (Or.inl ⟨hij, hmem⟩)
  · rintro ⟨c, hc⟩
    refine ⟨SimpleGraph.Coloring.mk c ?_⟩
    intro i j hadj
    rcases hadj with ⟨hij, hmem⟩ | ⟨hji, hmem⟩
    · exact hc i j hij hmem
    · exact Ne.symm (hc j i hji hmem)
