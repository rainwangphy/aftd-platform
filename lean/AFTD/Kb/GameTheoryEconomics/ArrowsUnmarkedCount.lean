import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsPos

/-!
# arrows_unmarked_count

Topic: combinatorial_games   Node: 0d0f864bab8d

Provenance: helper lemma. step towards arrows_twin_branch_reduction

The number of unmarked edges of G at the position p: edges of G on which neither orientation has been marked.
-/

open scoped Classical in
/-- The number of edges of G still available to be marked at position p. -/
noncomputable def arrows_unmarked_count {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (p : ArrowsPos V) : ℕ := (@Finset.filter (Sym2 V)
    (fun e => e.lift ⟨fun u v => p.1 u v = false ∧ p.1 v u = false, by
      intro u v
      exact propext and_comm⟩)
    (Classical.decPred _)
    G.edgeFinset).card
