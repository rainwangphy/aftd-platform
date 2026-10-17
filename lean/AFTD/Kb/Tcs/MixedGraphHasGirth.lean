import AFTD.Prelude
import AFTD.Kb.Tcs.MixedGraphHasCycle

/-!
# mixed_graph_has_girth

Topic: graphs   Node: 79a0de6ca461

Provenance: formalization of a published result. Source: arXiv:2610.14110 (New mixed cages, bounds and computational results), Sec. 2 (girth of a mixed graph).

A mixed graph has girth g: it has a cycle of length g and no shorter cycle.
-/

/-- `(E, A)` has girth `g`: a `g`-cycle exists and no `t`-cycle with `t < g` does. -/
def mixed_graph_has_girth {V : Type*} (E : SimpleGraph V) (A : V → V → Prop) (g : ℕ) : Prop :=
  mixed_graph_has_cycle E A g ∧ ∀ t < g, ¬ mixed_graph_has_cycle E A t
