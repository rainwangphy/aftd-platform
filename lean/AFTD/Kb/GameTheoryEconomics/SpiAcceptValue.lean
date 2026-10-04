import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiSignalValue
import AFTD.Kb.GameTheoryEconomics.SpiAccepted

/-!
# spi_accept_value

Topic: mechanism_design   Node: 25e2dcc8c1e1

Expected reward collected from player i on the event that it is reached and accepted.
-/

open Finset in
/-- Expected reward collected from player `i` on the event that the searcher reaches and accepts it (the sum of probability times posterior mean over accepted signals). -/
noncomputable def spi_accept_value {N K S : ℕ} (x w : Fin N → Fin K → ℝ) (φ : Fin N → Fin K → Fin S → ℝ)
    (T : ℝ) (i : Fin N) : ℝ :=
  ∑ s ∈ spi_accepted x w φ T i, spi_signal_value x w φ i s
