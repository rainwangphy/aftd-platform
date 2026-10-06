import AFTD.Prelude

/-!
# mms4_grid_value

Topic: fair_division   Node: 36edd48dd22e

Provenance: formalization of a published result. Source: arXiv:2610.06125 (On MMS allocations with few items), Table 1

Table 1 of arXiv:2610.06125: two agents, four goods in a 2 × 2 grid; nonempty bundles have value 1, except value 2 for bundles containing a whole row (agent 0) or a whole column (agent 1).
-/

/-- The two-agent, four-good instance of arXiv:2610.06125, Table 1: goods 0, 1, 2, 3 form the 2 × 2 grid with rows {0, 1}, {2, 3} and columns {0, 2}, {1, 3}; every nonempty bundle is worth 1, except that agent 0 values a bundle containing a row at 2 and agent 1 a bundle containing a column at 2. -/
def mms4_grid_value (i : Fin 2) (S : Finset (Fin 4)) : ℕ :=
  if S = ∅ then 0
  else if (i = 0 ∧ ({0, 1} ⊆ S ∨ {2, 3} ⊆ S)) ∨ (i = 1 ∧ ({0, 2} ⊆ S ∨ {1, 3} ⊆ S)) then 2
  else 1
