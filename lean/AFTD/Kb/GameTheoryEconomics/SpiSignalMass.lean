import AFTD.Prelude

/-!
# spi_signal_mass

Topic: mechanism_design   Node: b1b67652ac38

Probability of signal s of player i in the prophet search game with strategic reward signaling: sum over support points k of w_ik phi_ik(s).
-/

open Finset in
/-- Probability of signal `s` of player `i` in the prophet search game with strategic reward signaling (Tang–Xu–Zhang–Zhu): player `i`'s reward takes its `k`-th support value with probability `w i k`, and `φ i k s` is the probability that its scheme sends `s` given that value. -/
def spi_signal_mass {N K S : ℕ} (w : Fin N → Fin K → ℝ) (φ : Fin N → Fin K → Fin S → ℝ)
    (i : Fin N) (s : Fin S) : ℝ :=
  ∑ k, w i k * φ i k s
