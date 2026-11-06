import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.MaxcutUtility

/-!
# is_maxcut_neutral_pivot_safe

Topic: equilibria   Node: 7c5ae92ff0fc

Provenance: helper lemma.

No coalition can move the designated pivot while weakly improving its utility and strictly improving every other coalition member.
-/

def is_maxcut_neutral_pivot_safe {V : Type} [Fintype V]
    (G : SimpleGraph V) [DecidableRel G.Adj] {k : ℕ} (σ : V → Fin k) (u : V) : Prop := ∀ (C : Finset V) (τ : V → Fin k),
      u ∈ C → τ u ≠ σ u → (∀ x, x ∉ C → τ x = σ x) →
      maxcut_utility G σ u ≤ maxcut_utility G τ u →
      (∀ x ∈ C, x ≠ u → maxcut_utility G σ x < maxcut_utility G τ x) → False
