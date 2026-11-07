import AFTD.Prelude
import AFTD.Kb.Tcs.HasOrderedCopy

/-!
# ordered_ramsey_prop

Topic: graphs   Node: 42f0fddb84e7

Provenance: formalization of a published result. Source: arXiv:2611.08375 "New results on cyclic and ordered Ramsey numbers", Section 1

For ordered graphs H and H' and natural number N, ordered_ramsey_prop H H' N holds if for every graph G on Fin N, G contains an ordered copy of H or the complement Gᶜ contains an ordered copy of H'.
-/

/-- Every 2-edge-colouring of the complete ordered graph on N vertices contains a red copy of H or a blue copy of H'. -/
def ordered_ramsey_prop {α β : Type*} [LinearOrder α] [LinearOrder β]
    (H : SimpleGraph α) (H' : SimpleGraph β) (N : ℕ) : Prop := ∀ G : SimpleGraph (Fin N), has_ordered_copy G H ∨ has_ordered_copy Gᶜ H'
