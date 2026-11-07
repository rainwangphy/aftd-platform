import AFTD.Prelude
import AFTD.Kb.Optimization.IsMstFor

/-!
# is_mst_certificate

Topic: submodular   Node: 1d0b468c4ed5

Provenance: formalization of a published result. Source: scout/2610-40844-stochastic-minimum-spanning-tree-identification-with-binary.md:267

A partial realization β : G.edgeSet → Option Bool is an MST identification certificate for G if there exists a spanning tree T of G (T ≤ G with T.IsTree) such that for every full realization α : G.edgeSet → Bool extending β (meaning α e = b whenever β e = some b), T is a minimum spanning tree of G under α (is_mst_for G T α).
-/

open scoped Classical in
/-- A partial realization is an MST certificate if some spanning tree is an MST under every full extension. -/
def is_mst_certificate {V : Type*} [Fintype V] (G : SimpleGraph V) (β : G.edgeSet → Option Bool) : Prop := ∃ T ≤ G, T.IsTree ∧ ∀ α : G.edgeSet → Bool, (∀ e b, β e = some b → α e = b) → is_mst_for G T α
