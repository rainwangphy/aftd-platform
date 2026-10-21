import AFTD.Prelude

/-!
# ghz_matching_weight

Topic: quantum   Node: 74208b9a8d5d

Provenance: formalization of a published result. Source: scout/2610-22190-connectivity-bounds-for-ghz-graphs.md:155

For any type V : Type*, given an edge weight function w : Sym2 V → ℂ and a finite set of unordered pairs M : Finset (Sym2 V), the weight ghz_matching_weight w M is the product ∏ e ∈ M, w e.
-/

/-- The weight of a matching M is the product of the weights of its edges. -/
noncomputable def ghz_matching_weight {V : Type*} (w : Sym2 V → ℂ) (M : Finset (Sym2 V)) : ℂ := ∏ e ∈ M, w e
