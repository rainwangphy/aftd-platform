import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HungerIter

/-!
# hunger_recurrent_basin

Topic: combinatorial_games   Node: 3e0651b239d1

Provenance: formalization of a published result. Source: arXiv:2610.08949 Section 3, Prop 3.1

For n : ℕ with [NeZero n], a linearly ordered additive group K with one, a matrix P : Matrix (Fin n) (Fin n) K, and a natural number T, hunger_recurrent_basin P T is the set of vectors h : Fin n → K such that hunger_iter P T h = h.
-/

/-- The recurrent basin of a hunger game with minimal period T. -/
def hunger_recurrent_basin {n : ℕ} [NeZero n] {K : Type*} [LinearOrder K] [AddGroup K] [One K] (P : Matrix (Fin n) (Fin n) K) (T : ℕ) : Set (Fin n → K) := {h | hunger_iter P T h = h}
