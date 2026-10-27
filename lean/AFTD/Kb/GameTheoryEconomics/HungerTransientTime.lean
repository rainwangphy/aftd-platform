import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.HungerRecurrentBasin
import AFTD.Kb.GameTheoryEconomics.HungerIter

/-!
# hunger_transient_time

Topic: combinatorial_games   Node: 49dfabbd6c97

Provenance: formalization of a published result. Source: arXiv:2610.08949 after Thm 3.8

For a natural number n with [NeZero n], a rational matrix P : Matrix (Fin n) (Fin n) ℚ, a natural number T, and a rational vector h : Fin n → ℚ, hunger_transient_time P T h is the infimum sInf of the set of natural numbers t such that hunger_iter P t h belongs to hunger_recurrent_basin P T.
-/

/-- The transient time to reach the recurrent basin of a rational hunger game. -/
noncomputable def hunger_transient_time {n : ℕ} [NeZero n]
    (P : Matrix (Fin n) (Fin n) ℚ) (T : ℕ) (h : Fin n → ℚ) : ℕ := sInf {t : ℕ | hunger_iter P t h ∈ hunger_recurrent_basin P T}
