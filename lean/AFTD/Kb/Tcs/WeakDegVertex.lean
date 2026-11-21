import AFTD.Prelude
import AFTD.Kb.Tcs.WeakDegOp

/-!
# weak_deg_vertex

Topic: graphs   Node: f1f97eedd784

Provenance: formalization of a published result. Source: arXiv:2611.25850: Section 1

The vertex deleted by a weak degeneracy operation op : WeakDegOp V (mapping Del(v) to v and DelSave(v, w) to v).
-/

/-- The vertex deleted by a weak degeneracy operation. -/
def weak_deg_vertex {V : Type*} (op : WeakDegOp V) : V := match op with
  | .del v => v
  | .delSave v _ => v
