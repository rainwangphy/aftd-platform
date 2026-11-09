import AFTD.Prelude

/-!
# ocycap_crosses_cut

Topic: online_algorithms   Node: 7f3729b37f52

Provenance: formalization of a published result. Source: arXiv:2611.08570 Section 1.2, Section 3.1

For any type V, an unordered pair e : Sym2 V of vertices crosses a set of vertices C : Set V if there exist u, v : V such that e = s(u, v), u ∈ C, and v ∉ C.
-/

/-- An unordered pair e : Sym2 V crosses a set C : Set V if one endpoint is in C and the other is not. -/
def ocycap_crosses_cut {V : Type*} (e : Sym2 V) (C : Set V) : Prop := ∃ u v, e = s(u, v) ∧ u ∈ C ∧ v ∉ C
