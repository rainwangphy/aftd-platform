import AFTD.Prelude

/-!
# is_chordal

Topic: equilibria   Node: 418f52f80cd2

Provenance: formalization of a published result. Source: Dirac (1961), On rigid circuit graphs

A simple graph G is chordal if it contains no induced cycle of length four or greater.
-/

/-- A simple graph is chordal if it has no induced cycle of length at least 4. -/
def is_chordal {V : Type*} (G : SimpleGraph V) : Prop :=
  ∀ n : ℕ, 4 ≤ n → ¬ SimpleGraph.IsIndContained (SimpleGraph.cycleGraph n) G
