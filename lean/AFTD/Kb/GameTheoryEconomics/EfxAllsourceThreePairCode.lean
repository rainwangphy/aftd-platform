import AFTD.Prelude

/-!
# efx_allsource_three_pair_code

Topic: fair_division   Node: 1539c67ba3ef

Provenance: helper lemma. Four-agent envy-free one-charity three-split barrier for OP-7; SMT experiment 11699 and independent enumeration 11701. Both are evidence, not Lean proofs.

Encodes allocations in which only one of six designated pairs of original pairs may be split.
-/

def efx_allsource_three_pair_code (j : Fin 6) (q : Fin 7 → Fin 4) : Fin 9 → Fin 4 := ![q 0, (if (0 : Fin 4) = ![(0 : Fin 4),0,0,1,1,2] j then q 4 else if (0 : Fin 4) = ![(1 : Fin 4),2,3,2,3,3] j then q 5 else q 0), q 1, (if (1 : Fin 4) = ![(0 : Fin 4),0,0,1,1,2] j then q 4 else if (1 : Fin 4) = ![(1 : Fin 4),2,3,2,3,3] j then q 5 else q 1), q 2, (if (2 : Fin 4) = ![(0 : Fin 4),0,0,1,1,2] j then q 4 else if (2 : Fin 4) = ![(1 : Fin 4),2,3,2,3,3] j then q 5 else q 2), q 3, (if (3 : Fin 4) = ![(0 : Fin 4),0,0,1,1,2] j then q 4 else if (3 : Fin 4) = ![(1 : Fin 4),2,3,2,3,3] j then q 5 else q 3), q 6]
