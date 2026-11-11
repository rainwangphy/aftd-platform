import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.BalancedDraftValueOrder

/-!
# balanced_draft_value_order_iff

Topic: fair_division   Node: b36ab09c4619

Provenance: helper lemma. Definitions and auxiliary facts for OP-1493, the joint Gaussian limit for balanced sincere drafting.

In the induced order, a good is at most another exactly when its value is smaller, or the values agree and its index is at most the other index.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

theorem balanced_draft_value_order_iff {m : ℕ} (v : Fin m → ℝ) (g h : Fin m) :
    @LE.le (Fin m) (balanced_draft_value_order v).toLE g h ↔
      v g < v h ∨ (v g = v h ∧ g ≤ h) := by
  change toLex (v g, g) ≤ toLex (v h, h) ↔ _
  exact Prod.Lex.toLex_le_toLex
