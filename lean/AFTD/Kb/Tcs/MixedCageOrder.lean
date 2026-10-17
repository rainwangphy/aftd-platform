import AFTD.Prelude
import AFTD.Kb.Tcs.MixedGraphIsValid
import AFTD.Kb.Tcs.MixedGraphIsRegular
import AFTD.Kb.Tcs.MixedGraphHasCycle
import AFTD.Kb.Tcs.MixedGraphHasGirth

/-!
# mixed_cage_order

Topic: graphs   Node: 97416881b2a6

Provenance: formalization of a published result. Source: arXiv:2610.14110 (New mixed cages, bounds and computational results), Sec. 2 (mixed cages and their order n(r,z,g)).

n(r, z, g): the minimum order of an (r, z)-regular mixed graph of girth g (the order of an (r, z, g)-mixed cage).
-/

/-- `n(r, z, g)`: the least `n` such that some `(r, z)`-regular mixed graph on `Fin n` has girth `g` (0 if there is none). -/
noncomputable def mixed_cage_order (r z g : ℕ) : ℕ :=
  sInf {n | ∃ (E : SimpleGraph (Fin n)) (A : Fin n → Fin n → Prop),
    mixed_graph_is_valid E A ∧ mixed_graph_is_regular E A r z ∧ mixed_graph_has_girth E A g}
