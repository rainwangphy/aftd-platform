import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HungerStep

/-!
# hunger_iter

Topic: combinatorial_games   Node: 01a7e9d3a39d

Provenance: formalization of a published result. Source: arXiv:2610.08949 Eq (2.2)

For n : ℕ with [NeZero n], a linearly ordered additive group K with one, a matrix P : Matrix (Fin n) (Fin n) K, a natural number t, and an initial vector h : Fin n → K, hunger_iter P t h is the t-th iterate of hunger_step P applied to h, namely (hunger_step P)^[t] h.
-/

/-- Iterating the hunger game map t times from an initial state h. -/
def hunger_iter {n : ℕ} [NeZero n] {K : Type*} [LinearOrder K] [AddGroup K] [One K] (P : Matrix (Fin n) (Fin n) K) (t : ℕ) (h : Fin n → K) : Fin n → K := (hunger_step P)^[t] h
