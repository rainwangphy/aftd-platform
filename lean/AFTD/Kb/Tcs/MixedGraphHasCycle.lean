import AFTD.Prelude

/-!
# mixed_graph_has_cycle

Topic: graphs   Node: 302092980663

Provenance: formalization of a published result. Source: arXiv:2610.14110 (New mixed cages, bounds and computational results), Sec. 2 (cycles of a mixed graph).

A mixed graph has a cycle of length t ≥ 3: distinct vertices x_0, ..., x_{t-1} such that each x_i is joined to x_{i+1} (indices mod t) by an edge or by an arc directed from x_i to x_{i+1}.
-/

/-- `(E, A)` has a `t`-cycle: `t ≥ 3` pairwise distinct vertices `x 0, ..., x (t-1)` with an edge `x i — x (i+1)` or an arc `x i → x (i+1)` for every `i`, indices mod `t` (`finRotate`). The paper notes cycles have length at least 3: with distinct vertices no edge is used twice. -/
def mixed_graph_has_cycle {V : Type*} (E : SimpleGraph V) (A : V → V → Prop) (t : ℕ) : Prop :=
  3 ≤ t ∧ ∃ x : Fin t → V, Function.Injective x ∧
    ∀ i : Fin t, E.Adj (x i) (x (finRotate t i)) ∨ A (x i) (x (finRotate t i))
