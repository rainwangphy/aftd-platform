import AFTD.Prelude
import AFTD.Kb.Tcs.WeakDegOp

/-!
# weak_deg_next_bound

Topic: graphs   Node: a11fbb1c1c63

Provenance: formalization of a published result. Source: arXiv:2611.25850: Section 1

The updated integer-valued bound function f : V → ℤ after executing an operation op : WeakDegOp V on a finite set of vertices S : Finset V: for Del(v), any neighbor u of v in S has its bound decremented by 1 (and unchanged otherwise); for DelSave(v, w), any neighbor u of v in S other than w has its bound decremented by 1 (and unchanged otherwise).
-/

open Classical in
/-- Updated integer bound function after Del or DelSave on remaining vertex set S. -/
noncomputable def weak_deg_next_bound {V : Type*}
    (G : SimpleGraph V) (S : Finset V) (f : V → ℤ) :
    WeakDegOp V → (V → ℤ)
  | .del v => fun u => if u ∈ S ∧ G.Adj v u then f u - 1 else f u
  | .delSave v w => fun u => if u ∈ S ∧ u ≠ w ∧ G.Adj v u then f u - 1 else f u
