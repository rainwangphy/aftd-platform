import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimMisereComp

/-!
# slow_exact_nim_misere

Topic: combinatorial_games   Node: 0d50ffcf736e

Provenance: formalization of a published result. Source: arXiv:2611.14546, Section 1

The misère invariant slow_exact_nim_misere k n x of a position x : Fin n → ℕ in slow exact k-Nim on n piles is defined as slow_exact_nim_misere_comp k n (∑ i : Fin n, x i) x.
-/

/-- The misère invariant of a position in slow exact k-Nim on n piles, with terminal value 1. -/
def slow_exact_nim_misere (k n : ℕ) (x : Fin n → ℕ) : ℕ := slow_exact_nim_misere_comp k n (∑ i : Fin n, x i) x
