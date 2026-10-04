import AFTD.Prelude

/-!
# spi_signal_value

Topic: mechanism_design   Node: 8f8d62161600

Reward-weighted probability of signal s of player i: probability of s times the searcher's posterior mean reward given s.
-/

open Finset in
/-- Reward-weighted probability of signal `s` of player `i`: the probability of `s` times the searcher's posterior mean reward given `s`. -/
def spi_signal_value {N K S : ℕ} (x w : Fin N → Fin K → ℝ) (φ : Fin N → Fin K → Fin S → ℝ)
    (i : Fin N) (s : Fin S) : ℝ :=
  ∑ k, w i k * φ i k s * x i k
