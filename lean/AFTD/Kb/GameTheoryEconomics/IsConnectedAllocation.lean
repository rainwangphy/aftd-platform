import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsPathConnected
import AFTD.Kb.GameTheoryEconomics.BundleOf

/-!
# is_connected_allocation

Topic: fair_division   Node: c6b32a04fb73

An allocation is connected if every agent's bundle is connected on the path.
-/

/-- Every agent's bundle under `σ` is connected on the path. -/
def is_connected_allocation {m n : ℕ} (σ : Fin m → Fin n) : Prop :=
  ∀ i, is_path_connected (bundle_of σ i)
