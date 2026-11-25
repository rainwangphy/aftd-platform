import AFTD.Prelude

/-!
# MisereOutcome

Topic: combinatorial_games   Node: f72a34d4a1d4

Provenance: formalization of a published result. Source: arXiv:2611.29198 Section 2.1

The misère outcome of an impartial game position: P for a previous-player-winning position and N for a next-player-winning position.
-/

/-- The misère outcome type for impartial game positions, with values P and N. -/
inductive MisereOutcome : Type | P : MisereOutcome
| N : MisereOutcome
deriving DecidableEq, Repr
