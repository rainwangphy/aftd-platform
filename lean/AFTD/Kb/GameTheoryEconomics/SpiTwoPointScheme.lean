import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiTwoPointPoolProb

/-!
# spi_two_point_scheme

Topic: mechanism_design   Node: 83232cc16de8

The optimal scheme of Proposition 3.1 for a two-point reward embedded in S signals: high value sends signal 0, low value sends signal 0 with the pooling probability and signal 1 otherwise.
-/

/-- The optimal scheme of Prop. 3.1 for a two-point reward, embedded in `S` signals: the high value (index 0) always sends signal 0; the low value (index 1) sends signal 0 with probability `spi_two_point_pool_prob` and signal 1 otherwise. -/
noncomputable def spi_two_point_scheme (S : ℕ) (h l q T : ℝ) : Fin 2 → Fin S → ℝ := fun k s =>
  if k = 0 then (if s.val = 0 then 1 else 0)
  else if s.val = 0 then spi_two_point_pool_prob h l q T
  else if s.val = 1 then 1 - spi_two_point_pool_prob h l q T else 0
