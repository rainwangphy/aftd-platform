import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# op869_gadget_explicit_parameters

Topic: online_algorithms   Node: 4018ed796495

Provenance: helper lemma. arXiv:2610.41516, Lemmas 2.3 and 2.4

For q at least t at least one, 4 ceil(q/t) growth rounds give at least 2q colors and a complete binary construction fits within 2^(5 ceil(q/t)) vertices.
-/

/-- Explicit parameters for the bipartite gadget. -/
theorem op869_gadget_explicit_parameters (q t : ℕ) (ht : 1 ≤ t) (htq : t ≤ q) :
    let r := (q+t-1)/t
    2*q ≤ t + (4*r)*((t+1)/2) ∧ 2^(4*r+1) ≤ 2^(5*r) := by
  dsimp only
  let r := (q+t-1)/t
  change 2*q ≤ t + (4*r)*((t+1)/2) ∧ 2^(4*r+1) ≤ 2^(5*r)
  have hpos : 0 < t := by omega
  have hdiv := Nat.mod_add_div (q+t-1) t
  have hmod := Nat.mod_lt (q+t-1) hpos
  have hq : q ≤ t*r := by dsimp [r]; omega
  have hr : 1 ≤ r := by
    dsimp [r]
    apply Nat.div_pos
    · omega
    · omega
  have hhalf : t ≤ 2*((t+1)/2) := by omega
  have hmul := Nat.mul_le_mul_right r hhalf
  constructor
  · nlinarith
  · exact Nat.pow_le_pow_right (by omega : 0 < 2) (by omega)
