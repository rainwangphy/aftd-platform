import AFTD.Prelude

/-!
# efx_anchor_lock_values

Topic: fair_division   Node: fbcb8c8a1aeb

Provenance: helper lemma. Nondegenerate no-singleton four-agent Pareto-maximal partial EFX obstruction, experiments 11500–11507; locked-good lift of arXiv:2002.05119 Section 5.

The explicit positive twelve-good anchor-and-lock matrix: three anchors at goods 7,8,9 and two locked goods 10,11, with the first seven goods inherited from the locked example.
-/

def efx_anchor_lock_values : Fin 4 → Fin 12 → ℕ := ![![81,21,121,21,1,171,11,1000,1000,1000,1162,1162], ![51,1,91,41,101,1,31,1000,1000,1000,1151,1151], ![1,1,1,1,91,101,21,1000,1000,1000,1100,1100], ![1,1,1,1,1,1,1,1,1,1,20,20]]
