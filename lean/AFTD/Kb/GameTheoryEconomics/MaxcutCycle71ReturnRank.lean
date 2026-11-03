import AFTD.Prelude

/-!
# maxcut_cycle71_return_rank

Topic: equilibria   Node: bdc24f3141be

Provenance: helper lemma. The explicit 71-vertex unweighted minimal-deviation cycle for the potential-function question in arXiv:1810.09278, Section 7; experiments 12443, 12444, 12450 and 12452.

The order in which each core vertex is restored during the displayed 71-vertex cycle.
-/

def maxcut_cycle71_return_rank (v : Fin 71) : ℕ :=
  if 24 ≤ v.val then v.val - 24 else if 8 ≤ v.val then v.val else v.val + 24
