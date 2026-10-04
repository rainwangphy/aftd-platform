import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiSignalMass
import AFTD.Kb.GameTheoryEconomics.SpiSignalValue
import AFTD.Kb.GameTheoryEconomics.SpiAccepted
import AFTD.Kb.GameTheoryEconomics.SpiAcceptProb
import AFTD.Kb.GameTheoryEconomics.SpiAcceptValue

/-!
# spi_accept_congr

Topic: mechanism_design   Node: 191d4736e5e2

Acceptance probability and accepted value of player i depend only on player i's own scheme.
-/

/-- Acceptance probability and accepted value of player `i` only depend on player `i`'s own scheme. -/
lemma spi_accept_congr {N K S : ℕ} (x w : Fin N → Fin K → ℝ) (φ φ' : Fin N → Fin K → Fin S → ℝ)
    (T : ℝ) (i : Fin N) (h : φ i = φ' i) :
    spi_accept_prob x w φ T i = spi_accept_prob x w φ' T i ∧
      spi_accept_value x w φ T i = spi_accept_value x w φ' T i := by
  simp only [spi_accept_prob, spi_accept_value, spi_accepted, spi_signal_mass, spi_signal_value, h]
  exact ⟨rfl, rfl⟩
