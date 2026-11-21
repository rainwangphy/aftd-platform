import AFTD.Prelude
import AFTD.Kb.Tcs.WeakDegOp

/-!
# weak_deg_op_avail

Topic: graphs   Node: 5d311e8dff13

Provenance: formalization of a published result. Source: arXiv:2611.25850: Section 1

The availability of a weak degeneracy operation: f(v) + 1 for Del(v), and f(v) - f(w) for DelSave(v, w).
-/

/-- Availability of an operation: f(v) + 1 for Del, f(v) - f(w) for DelSave. -/
def weak_deg_op_avail {V : Type*} (f : V → ℤ) : WeakDegOp V → ℤ
  | .del v => f v + 1
  | .delSave v w => f v - f w
