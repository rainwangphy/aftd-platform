import AFTD.Prelude

/-!
# efx_min_cycle_baseline

Topic: fair_division   Node: 0e58d7fd2fd3

Provenance: helper lemma. Minimum-cardinality champion-cycle swap obstruction for OP-7, experiments 11442–11449; comparison with arXiv:2002.05119 Section 3.1.

The initial utilities of the four agents.
-/

def efx_min_cycle_baseline : Fin 4 → ℕ := ![18,18,36,18]
