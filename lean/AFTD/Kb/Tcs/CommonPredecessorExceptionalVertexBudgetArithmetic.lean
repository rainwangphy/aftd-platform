import AFTD.Prelude

/-!
# common_predecessor_exceptional_vertex_budget_arithmetic

Topic: graphs   Node: 3327db1acf8a

Provenance: helper lemma. Auxiliary-graph transfer and counting steps for the OP-110 campaign.

If z≤1, d≥47, and d≤6t≤d+z, then t+40≤d+z.
-/

theorem common_predecessor_exceptional_vertex_budget_arithmetic (z d t : ℕ)
    (hz : z ≤ 1) (hd : 47 ≤ d) (hlo : d ≤ 6 * t) (hhi : 6 * t ≤ d + z) :
    t + 40 ≤ d + z := by
  omega
