import AFTD.Prelude

/-!
# balanced_draft_value_order

Topic: fair_division   Node: 8732af7d58f9

Provenance: helper lemma. Definitions and auxiliary facts for OP-1493, the joint Gaussian limit for balanced sincere drafting.

The strict preference order induced by a real value vector, ordered first by increasing value and then by increasing good index; hence a maximum is a highest-valued good and ties favor the larger index.
-/

open MeasureTheory ProbabilityTheory Filter
open scoped BigOperators Topology

noncomputable def balanced_draft_value_order {m : ℕ} (v : Fin m → ℝ) : LinearOrder (Fin m) :=
  LinearOrder.lift' (fun g => toLex (v g, g)) (by
    intro g h heq
    exact congrArg Prod.snd (congrArg ofLex heq))
