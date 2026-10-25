import AFTD.Prelude

/-!
# arrows_num_markable_edges

Topic: combinatorial_games   Node: ee4dfa883518

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 2.2

The number of markable edges of a finite simple graph T is the number of edges in T that are not pendant (neither of whose endpoints has degree 1 in T).
-/

/-- The number of markable (non-pendant) edges in a graph T. -/
noncomputable def arrows_num_markable_edges {V : Type*} [Fintype V] [DecidableEq V] (T : SimpleGraph V) [DecidableRel T.Adj] : ℕ := (@Finset.filter (Sym2 V)
    (fun e => e.lift ⟨fun u v => T.degree u ≠ 1 ∧ T.degree v ≠ 1, by
      intro u v
      exact propext and_comm⟩)
    (Classical.decPred _)
    T.edgeFinset).card
