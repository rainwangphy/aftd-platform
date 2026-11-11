import AFTD.Prelude
import AFTD.Kb.Tcs.ZeroForced

/-!
# is_zero_forcing_set

Topic: graphs   Node: 1c7e4fa4f90c

Provenance: formalization of a published result. Source: arXiv:2611.11352 Section 1

A set of vertices S is a zero forcing set of G if its zero forcing closure contains all vertices of G.
-/

/-- A zero forcing set is one whose closure is the entire vertex set. -/
def is_zero_forcing_set {V : Type*} (G : SimpleGraph V) (S : Set V) : Prop := ∀ v, ZeroForced G S v
