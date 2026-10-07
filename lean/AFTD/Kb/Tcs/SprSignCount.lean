import AFTD.Prelude

/-!
# spr_sign_count

Topic: learning   Node: 302920501781

Provenance: formalization of a published result. Source: arXiv:2610.07623 (Explicit asymptotic bounds for sequential calibration beyond T^{2/3}), Sec. 2.2 (payoff of the sign-preservation-with-reuse game)

The number of signs on a board of the sign-preservation-with-reuse game with n cells, each empty or holding a plus or a minus.
-/

/-- Number of signs on a board of the sign-preservation-with-reuse game: a board has `n` cells, each empty (`none`), holding a plus (`some true`) or holding a minus (`some false`). -/
def spr_sign_count {n : ℕ} (b : Fin n → Option Bool) : ℕ :=
  (Finset.univ.filter fun i => (b i).isSome).card
