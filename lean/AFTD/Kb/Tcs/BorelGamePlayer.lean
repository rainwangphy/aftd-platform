import AFTD.Prelude

/-!
# BorelGamePlayer

Topic: automata   Node: c0903a11b795

Provenance: formalization of a published result. Source: arXiv:2611.10136, Def. 10

The two players in a prioritized Borel game, Eve and Adam.
-/

/-- The two players in a game: Eve and Adam. -/
inductive BorelGamePlayer where
  | Eve : BorelGamePlayer
  | Adam : BorelGamePlayer
