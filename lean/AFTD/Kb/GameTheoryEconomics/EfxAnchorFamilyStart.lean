import AFTD.Prelude

/-!
# efx_anchor_family_start

Topic: fair_division   Node: 15af90bce183

Provenance: helper lemma. Unbounded common-anchor and multi-lock extension of the OP-7 Pareto-maximal partial EFX obstruction; experiments 11503, 11509 and 11511.

Keep the original seven-good partial allocation, assign r anchors to each original agent in order, and give all s locked goods to agent 3; label 4 means unallocated.
-/

def efx_anchor_family_start (r s : ℕ) : Fin ((7+(r+r+r))+s) → Fin 5 := Fin.addCases
  (Fin.addCases ![(1 : Fin 5),0,0,0,1,2,4]
    (fun g : Fin (r+r+r) => if (g : ℕ) < r then 0 else if (g : ℕ) < r+r then 1 else 2))
  (fun _ : Fin s => 3)
