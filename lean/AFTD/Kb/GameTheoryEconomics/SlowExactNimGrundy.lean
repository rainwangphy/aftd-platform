import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimGrundyComp

/-!
# slow_exact_nim_grundy

Topic: combinatorial_games   Node: 13c3040604e7

Provenance: formalization of a published result. Source: arXiv:2611.14546, Section 1

The Sprague-Grundy value slow_exact_nim_grundy k n x of a position x : Fin n → ℕ in slow exact k-Nim on n piles is defined as slow_exact_nim_grundy_comp k n (∑ i : Fin n, x i) x.
-/

/-- The Sprague-Grundy value of a position in slow exact k-Nim on n piles. -/
def slow_exact_nim_grundy (k n : ℕ) (x : Fin n → ℕ) : ℕ := slow_exact_nim_grundy_comp k n (∑ i, x i) x
