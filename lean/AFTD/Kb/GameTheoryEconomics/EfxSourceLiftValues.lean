import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPartialNatUtility

/-!
# efx_source_lift_values

Topic: fair_division   Node: 80d2e3a5929c

Provenance: helper lemma. General two-lock reduction from a partial EFX Pareto barrier to isolated-source utility loss; specialized in experiments 11561–11562.

Scale old values by 3, add unequal source locks, and give the new agent two high-valued locks.
-/

def efx_source_lift_values {n m : ℕ}
  (v : Fin n → Fin m → ℕ) (b : Fin n → ℕ) : Fin (n+1) → Fin (m+2) → ℕ := Fin.lastCases
  (Fin.addCases (fun _ : Fin m => 1) (fun _ : Fin 2 => m+1))
  (fun i : Fin n => Fin.addCases (fun g : Fin m => 3 * v i g)
    (fun k : Fin 2 => if k = 0 then 3 * b i - 2 else 1))
