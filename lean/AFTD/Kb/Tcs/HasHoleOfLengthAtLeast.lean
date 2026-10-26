import AFTD.Prelude

/-!
# HasHoleOfLengthAtLeast

Topic: graphs   Node: 6739dba0d180

Provenance: helper lemma. step towards op_292_cop_number_p6_claw_free

A graph G has a hole of length at least t if, for some n with t ≤ n and n ≥ 4, G contains an induced copy of the cycle C_n on n vertices. (A hole is an induced cycle of length at least 4.)
-/

/-- G has a hole (an induced cycle) of length at least `t`. -/
def HasHoleOfLengthAtLeast {V : Type*} (G : SimpleGraph V) (t : ℕ) : Prop := ∃ n : ℕ, t ≤ n ∧ 4 ≤ n ∧ SimpleGraph.IsIndContained (SimpleGraph.cycleGraph n) G
