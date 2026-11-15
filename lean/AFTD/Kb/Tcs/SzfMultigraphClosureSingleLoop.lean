import AFTD.Prelude
import AFTD.Kb.Tcs.SzfMultigraphClosure
import AFTD.Kb.Tcs.SzfMultiForced

/-!
# szf_multigraph_closure_single_loop

Topic: graphs   Node: 4dabb56c7230

Provenance: helper lemma. sanity lemma for szf_multigraph_closure (arXiv:2611.15741 Section 1: a single loop lets a vertex self-force)

A vertex with a single loop and no other edges forces itself from the empty filled set.
-/

theorem szf_multigraph_closure_single_loop :
    szf_multigraph_closure (fun (_ : Unit) (_ : Unit) => 1) ∅ = Set.univ := by
  ext ⟨⟩
  simp only [szf_multigraph_closure, Set.mem_univ, iff_true]
  refine SzfMultiForced.step () () rfl fun x hx => (hx (Subsingleton.elim x ())).elim
