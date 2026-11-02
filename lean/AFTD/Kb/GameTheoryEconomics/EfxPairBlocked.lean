import AFTD.Prelude

/-!
# efx_pair_blocked

Topic: fair_division   Node: 93d497af7922

Provenance: helper lemma. step towards efx_allsource_equal_pairs_ir_completion

Agent i blocks the old pair p when the charity good is worth strictly more to her than one of the two goods of pair p; this is exactly the condition under which, if some agent held all of p together with charity, i would envy her even after deleting one good.
-/

/-- Agent i blocks old pair p if charity is worth more to her than one of the two goods of p. -/
def efx_pair_blocked (v : Fin 4 → Fin 9 → ℝ) (i p : Fin 4) : Prop := v i 8 > v i (![0,2,4,6] p) ∨ v i 8 > v i (![1,3,5,7] p)
