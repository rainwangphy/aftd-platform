import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockValues
import AFTD.Kb.GameTheoryEconomics.EfxParetoLockBaseline

/-!
# efx_anchor_family_values

Topic: fair_division   Node: c14acbca2323

Provenance: helper lemma. Unbounded common-anchor and multi-lock extension of the OP-7 Pareto-maximal partial EFX obstruction; experiments 11503, 11509 and 11511.

Keep the first seven original goods with values scaled by s−1 for the first three agents and value 1 for the fourth. Append 3r common anchors worth (s−1)*1000*(s+1) to original agents and 1 to the fourth. Append s locked goods, each worth r*1000*(s+1) plus the original baseline minus 1 to an original agent and 8+3r to the fourth.
-/

def efx_anchor_family_values (r s : ℕ) : Fin 4 → Fin ((7+(r+r+r))+s) → ℕ := fun i => Fin.addCases
  (Fin.addCases (fun g : Fin 7 => if i = 3 then 1 else (s-1) * efx_pareto_lock_values i g.castSucc)
    (fun _ : Fin (r+r+r) => if i = 3 then 1 else (s-1) * (1000*(s+1))))
  (fun _ : Fin s => if i = 3 then 8+3*r else r*(1000*(s+1)) + efx_pareto_lock_baseline i - 1)
