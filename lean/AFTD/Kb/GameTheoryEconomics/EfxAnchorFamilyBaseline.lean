import AFTD.Prelude

/-!
# efx_anchor_family_baseline

Topic: fair_division   Node: f8d894633c2f

Provenance: helper lemma. Unbounded common-anchor and multi-lock extension of the OP-7 Pareto-maximal partial EFX obstruction; experiments 11503, 11509 and 11511.

The starting utilities in the r-anchor/s-lock extension.
-/

def efx_anchor_family_baseline (r s : ℕ) : Fin 4 → ℕ := ![(s-1)*(r*(1000*(s+1))+163), (s-1)*(r*(1000*(s+1))+152), (s-1)*(r*(1000*(s+1))+101), s*(8+3*r)]
