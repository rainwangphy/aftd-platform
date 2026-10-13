import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphInvert

/-!
# digraph_invert_invert

Topic: graphs   Node: 56ab83555bd3

Provenance: helper lemma. Sanity lemma for digraph_invert (arXiv:2610.13798, Sec. 1).

Inverting the same vertex set twice gives back the digraph.
-/

theorem digraph_invert_invert {V : Type*} (D : Digraph V) (X : Set V) :
    digraph_invert (digraph_invert D X) X = D := by
  ext x y
  simp only [digraph_invert]
  by_cases hx : x ∈ X <;> by_cases hy : y ∈ X <;> simp [hx, hy]
