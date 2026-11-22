import AFTD.Prelude
import AFTD.Kb.Tcs.MulticolorRamseyProperty

/-!
# multicolor_ramsey_number

Topic: combinatorics   Node: 97ec102757fa

Provenance: formalization of a published result. Source: arXiv:2611.19312 Section 1

For a simple graph H on vertex type V and a natural number r, the multicolor Ramsey number multicolor_ramsey_number H r is the infimum in ℕ of the set of natural numbers N such that every r-edge-coloring of the complete graph on Fin N contains a monochromatic copy of H.
-/

/-- Multicolor Ramsey number: the least N such that every r-edge-coloring of K_N contains a monochromatic copy of H. -/
noncomputable def multicolor_ramsey_number {V : Type*} (H : SimpleGraph V) (r : ℕ) : ℕ :=
  sInf {N : ℕ | multicolor_ramsey_property H r N}
