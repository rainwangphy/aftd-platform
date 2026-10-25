import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.ArrowsTreeGrundy

/-!
# arrows_realizable_grundy_values

Topic: combinatorial_games   Node: 8b25af830375

Provenance: formalization of a published result. Source: arXiv:2610.15145 Section 5.1 & Theorem 7.3

The set of natural numbers g such that there exists a finite tree G (a simple graph G on a finite type V satisfying G.IsTree) with arrows_tree_grundy G = g.
-/

/-- The set of realizable Grundy values of the Game of Arrows on finite trees. -/
def arrows_realizable_grundy_values : Set ℕ := { g : ℕ | ∃ (V : Type) (_ : Fintype V) (_ : DecidableEq V) (G : SimpleGraph V) (_ : DecidableRel G.Adj) (_ : G.IsTree),
      arrows_tree_grundy G = g }
