import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.SpiPlayerPayoff
import AFTD.Kb.GameTheoryEconomics.SpiIsScheme

/-!
# spi_is_equilibrium

Topic: mechanism_design   Node: 88e22ad74074

Nash equilibrium of the players' signaling game induced by a static threshold T: no player can raise its selection probability by unilaterally switching schemes.
-/

/-- Nash equilibrium of the players' signaling game induced by the static threshold `T`: no player can raise its selection probability by switching to another scheme. -/
def spi_is_equilibrium {N K S : ℕ} (x w : Fin N → Fin K → ℝ) (T : ℝ) (φ : Fin N → Fin K → Fin S → ℝ) : Prop :=
  (∀ i, spi_is_scheme (φ i)) ∧
    ∀ i (ψ : Fin K → Fin S → ℝ), spi_is_scheme ψ →
      spi_player_payoff x w (Function.update φ i ψ) T i ≤ spi_player_payoff x w φ T i
