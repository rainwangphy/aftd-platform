import AFTD.Prelude
import AFTD.Kb.Tcs.SzfMultigraphClosure
import AFTD.Kb.Tcs.SzfMultiForced

/-!
# szf_multigraph_closure_double_loop

Topic: graphs   Node: eb680ef476a4

Provenance: helper lemma. sanity lemma for szf_multigraph_closure (arXiv:2611.15741 Section 1: a double loop blocks self-forcing)

A vertex with a double loop and no other edges is not forced from the empty filled set.
-/

theorem szf_multigraph_closure_double_loop :
    szf_multigraph_closure (fun (_ : Unit) (_ : Unit) => 2) ∅ = ∅ := by
  ext v
  constructor
  · intro h
    induction h with
    | init v hv => simpa using hv
    | step u w huw _ _ => simp at huw
  · intro h
    simpa using h
