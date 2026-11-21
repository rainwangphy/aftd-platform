import AFTD.Prelude
import AFTD.Kb.Tcs.WeakDegOp

/-!
# weak_deg_is_legal

Topic: graphs   Node: 7cb2059280d3

Provenance: formalization of a published result. Source: arXiv:2611.25850: Section 1

For a simple graph G on vertex type V, a finite set of vertices S : Finset V, an integer-valued bound function f : V → ℤ, and an operation op : WeakDegOp V: Del(v) is legal if v ∈ S and 0 ≤ f(v); DelSave(v, w) is legal if v ∈ S, w ∈ S, G.Adj v w, 0 ≤ f(v), and f(w) < f(v).
-/

/-- Legality condition for a weak degeneracy operation on a finite vertex set S. -/
def weak_deg_is_legal {V : Type*} (G : SimpleGraph V) (S : Finset V) (f : V → ℤ) :
    WeakDegOp V → Prop
  | .del v => v ∈ S ∧ 0 ≤ f v
  | .delSave v w => v ∈ S ∧ w ∈ S ∧ G.Adj v w ∧ 0 ≤ f v ∧ f w < f v
