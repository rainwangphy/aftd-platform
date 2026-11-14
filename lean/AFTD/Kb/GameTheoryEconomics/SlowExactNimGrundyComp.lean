import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.FinsetMex
import AFTD.Kb.GameTheoryEconomics.SlowExactNimFollowers

/-!
# slow_exact_nim_grundy_comp

Topic: combinatorial_games   Node: f86d21859b36

Provenance: formalization of a published result. Source: arXiv:2611.14546, Section 1

For natural numbers k and n, fuel : ℕ, and position x : Fin n → ℕ, the fuel-bounded Sprague-Grundy value slow_exact_nim_grundy_comp k n fuel x is 0 when fuel = 0, and when fuel = fuel' + 1 it is finset_mex applied to the image of slow_exact_nim_followers k n x under slow_exact_nim_grundy_comp k n fuel'.
-/

/-- Fuel-bounded Sprague-Grundy evaluation for slow exact k-Nim. -/
def slow_exact_nim_grundy_comp (k n : ℕ) : ℕ → (Fin n → ℕ) → ℕ
| 0, _ => 0
| fuel + 1, x =>
  finset_mex ((slow_exact_nim_followers k n x).image (slow_exact_nim_grundy_comp k n fuel))
