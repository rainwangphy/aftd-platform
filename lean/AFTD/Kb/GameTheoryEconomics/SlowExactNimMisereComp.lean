import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SlowExactNimFollowers
import AFTD.Kb.GameTheoryEconomics.FinsetMex

/-!
# slow_exact_nim_misere_comp

Topic: combinatorial_games   Node: f3c44f86e8ff

Provenance: formalization of a published result. Source: arXiv:2611.14546, Section 1

For natural numbers k and n, fuel : ℕ, and position x : Fin n → ℕ, the fuel-bounded misère invariant slow_exact_nim_misere_comp k n fuel x is 1 when fuel = 0 or when x has no legal followers, and when fuel = fuel' + 1 and x has legal followers it is finset_mex applied to the image of slow_exact_nim_followers k n x under slow_exact_nim_misere_comp k n fuel'.
-/

/-- Fuel-bounded computation of the misère invariant for slow exact k-Nim on n piles. -/
def slow_exact_nim_misere_comp (k n : ℕ) : ℕ → (Fin n → ℕ) → ℕ
| 0, _ => 1
| fuel + 1, x =>
  if (slow_exact_nim_followers k n x).Nonempty then
    finset_mex ((slow_exact_nim_followers k n x).image (slow_exact_nim_misere_comp k n fuel))
  else
    1
