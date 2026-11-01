import AFTD.Prelude

/-!
# efx_pareto_lock_encode

Topic: fair_division   Node: 58d272459727

Provenance: helper lemma. Four-agent locked-good lift of the partial EFX Pareto barrier in arXiv:2002.05119, Section 5; experiments 11454–11457.

Encode a partial allocation of the seven original goods to agents 0, 1, 2, or charity, while assigning the locked good 7 to agent 3.
-/

def efx_pareto_lock_encode (q : Fin 7 → Fin 4) : Fin 8 → Fin 5 := Fin.lastCases (3 : Fin 5) (fun g => if q g = 3 then 4 else (q g).castSucc)
