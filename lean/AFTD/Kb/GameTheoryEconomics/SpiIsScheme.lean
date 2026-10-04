import AFTD.Prelude

/-!
# spi_is_scheme

Topic: mechanism_design   Node: 98809fe8c8a4

A signaling scheme of one player: for every support point a probability distribution over the S signals.
-/

open Finset in
/-- A signaling scheme of one player: for every support point, a probability distribution over the `S` signals. -/
def spi_is_scheme {K S : ℕ} (ψ : Fin K → Fin S → ℝ) : Prop :=
  (∀ k s, 0 ≤ ψ k s) ∧ ∀ k, ∑ s, ψ k s = 1
