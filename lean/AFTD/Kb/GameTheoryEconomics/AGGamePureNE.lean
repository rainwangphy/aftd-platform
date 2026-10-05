import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AGGame
import AFTD.Kb.GameTheoryEconomics.AgCnt

/-!
# AGGame.PureNE

Topic: equilibria   Node: 83b92d565d5d

The pure profile σ is an ε-approximate pure Nash equilibrium.
-/

/-- The pure profile `σ` is an `ε`-approximate pure Nash equilibrium. -/
def AGGame.PureNE {n s : ℕ} (G : AGGame n s) (ε : ℚ) (σ : Fin n → Fin s) : Prop :=
  ∀ p : Fin n, ∀ j : Fin s, G.u p j (agCnt σ p) ≤ G.u p (σ p) (agCnt σ p) + ε
