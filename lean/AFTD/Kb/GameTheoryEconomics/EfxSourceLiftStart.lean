import AFTD.Prelude

/-!
# efx_source_lift_start

Topic: fair_division   Node: b4c68b83868b

Provenance: helper lemma. General two-lock reduction from a partial EFX Pareto barrier to isolated-source utility loss; specialized in experiments 11561–11562.

Keep all old owners and charity positions, and give both new locks to the new agent.
-/

def efx_source_lift_start {n m : ℕ} (σ : Fin m → Fin (n+1)) : Fin (m+2) → Fin ((n+1)+1) := Fin.addCases
  (fun g : Fin m => Fin.lastCases (Fin.last (n+1))
    (fun i : Fin n => i.castSucc.castSucc) (σ g))
  (fun _ : Fin 2 => (Fin.last n).castSucc)
