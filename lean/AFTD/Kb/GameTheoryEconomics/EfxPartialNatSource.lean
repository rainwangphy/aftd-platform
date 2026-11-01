import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.EfxPartialNatUtility

/-!
# efx_partial_nat_source

Topic: fair_division   Node: f7e6a31db7c7

Provenance: helper lemma. Iterated two-lock source lift of the three-agent partial EFX Pareto barrier; experiment 11578.

An agent is a source of the strict-envy graph if no agent strictly envies her bundle.
-/

def efx_partial_nat_source {n m : ℕ} (v : Fin n → Fin m → ℕ)
  (σ : Fin m → Fin (n+1)) (i : Fin n) : Prop := ∀ j : Fin n, (∑ g : Fin m, if σ g = i.castSucc then v j g else 0) ≤ efx_partial_nat_utility v σ j
