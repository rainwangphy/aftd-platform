import AFTD.Prelude

/-!
# good_slopes_fiber15_form

Topic: elementary_number_theory   Node: c611aef51bee

Provenance: helper lemma. Projection forms used in the fiber analysis of OP-1027; compare arXiv:2611.04551, Section 9.

For a direction a and a point (x,y) over the residues modulo 15, return y + a x.
-/

def good_slopes_fiber15_form (a : ZMod 15) (p : ZMod 15 × ZMod 15) : ZMod 15 := p.2 + a * p.1
