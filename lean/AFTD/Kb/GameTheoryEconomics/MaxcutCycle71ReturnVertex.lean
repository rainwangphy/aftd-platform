import AFTD.Prelude

/-!
# maxcut_cycle71_return_vertex

Topic: equilibria   Node: be1c8a33f18e

Provenance: helper lemma. The explicit 71-vertex unweighted minimal-deviation cycle for the potential-function question in arXiv:1810.09278, Section 7; experiments 12443, 12444, 12450 and 12452.

The core vertex restored at each of the 32 singleton stages.
-/

def maxcut_cycle71_return_vertex (i : Fin 32) : Fin 71 :=
  ⟨if i.val < 8 then i.val + 24 else if i.val < 24 then i.val else i.val - 24, by
    have hi := i.isLt
    split_ifs <;> omega⟩
