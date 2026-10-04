import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiSignalMass
import AFTD.Kb.GameTheoryEconomics.SpiAccepted

/-!
# spi_accept_prob

Topic: mechanism_design   Node: e89170bd7794

Probability that the searcher accepts player i when she reaches it.
-/

open Finset in
/-- Probability that the searcher accepts player `i` when she reaches it. -/
noncomputable def spi_accept_prob {N K S : ℕ} (x w : Fin N → Fin K → ℝ) (φ : Fin N → Fin K → Fin S → ℝ)
    (T : ℝ) (i : Fin N) : ℝ :=
  ∑ s ∈ spi_accepted x w φ T i, spi_signal_mass w φ i s
