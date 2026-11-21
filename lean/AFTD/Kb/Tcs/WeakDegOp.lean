import AFTD.Prelude

/-!
# WeakDegOp

Topic: graphs   Node: 2138cea0de5c

Provenance: formalization of a published result. Source: arXiv:2611.25850: Section 1

An operation in a weak degeneracy sequence, either deleting a vertex v (Del) or deleting v while saving a neighbor w (DelSave).
-/

/-- An operation in a weak degeneracy sequence: Del(v) or DelSave(v, w). -/
inductive WeakDegOp (V : Type*) where
  | del (v : V) : WeakDegOp V
  | delSave (v w : V) : WeakDegOp V
