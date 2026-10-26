import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsTreeSpecial

/-!
# is_piece_thread

Topic: combinatorial_games   Node: 186008e951bd

Provenance: formalization of a published result. Source: arXiv:2610.15145, Section 10 and Question 11.4

A thread of a piece of a tree T is a path of length at least 1 whose interior vertices have degree 2 and are not special, and whose endpoints are either special or have degree at least 3.
-/

/-- A thread of a piece in a tree is a maximal path whose interior vertices have degree 2 and are not special. -/
def is_piece_thread {V : Type*} [Fintype V] [DecidableEq V]
    (T : SimpleGraph V) [DecidableRel T.Adj] {u v : V} (p : T.Walk u v) : Prop := p.IsPath ∧ 1 ≤ p.length ∧
  (is_tree_special T u ∨ (3 ≤ T.degree u ∧ ¬ is_tree_special T u)) ∧
  (is_tree_special T v ∨ (3 ≤ T.degree v ∧ ¬ is_tree_special T v)) ∧
  ∀ x ∈ (p.support.drop 1).dropLast, T.degree x = 2 ∧ ¬ is_tree_special T x
