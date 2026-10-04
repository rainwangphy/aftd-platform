import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiSignalMass
import AFTD.Kb.GameTheoryEconomics.SpiSignalValue

/-!
# spi_accepted

Topic: mechanism_design   Node: 9b397b775360

The signals of player i on which the static-threshold searcher with threshold T stops: those with posterior mean at least T.
-/

open Finset in
/-- The signals of player `i` on which the static-threshold searcher with threshold `T` stops: those whose posterior mean reward is at least `T` (written `T * mass ≤ value`, so null signals are harmless). -/
noncomputable def spi_accepted {N K S : ℕ} (x w : Fin N → Fin K → ℝ) (φ : Fin N → Fin K → Fin S → ℝ)
    (T : ℝ) (i : Fin N) : Finset (Fin S) :=
  univ.filter fun s => T * spi_signal_mass w φ i s ≤ spi_signal_value x w φ i s
