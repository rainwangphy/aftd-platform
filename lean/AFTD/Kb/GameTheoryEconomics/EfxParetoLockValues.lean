import AFTD.Prelude

/-!
# efx_pareto_lock_values

Topic: fair_division   Node: db2f1a59af34

Provenance: helper lemma. Four-agent locked-good lift of the partial EFX Pareto barrier in arXiv:2002.05119, Section 5; experiments 11454–11457.

The explicit positive natural valuation rows (81,21,121,21,1,171,11,428), (51,1,91,41,101,1,31,318), (1,1,1,1,91,101,21,218), and (1,1,1,1,1,1,1,8).
-/

def efx_pareto_lock_values : Fin 4 → Fin 8 → ℕ := ![![81,21,121,21,1,171,11,428], ![51,1,91,41,101,1,31,318], ![1,1,1,1,91,101,21,218], ![1,1,1,1,1,1,1,8]]
