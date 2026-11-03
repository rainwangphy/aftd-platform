import AFTD.Prelude
import AFTD.Kb.Tcs.MultigraphTruncation

/-!
# multigraph_truncation_adj_external

Topic: graphs   Node: 01b08aad7a45

Provenance: helper lemma. sanity lemma for multigraph_truncation

Sanity: the two ports (u, e), (v, e) of an edge e with distinct endpoints u ≠ v are adjacent in the truncation (the external edge).
-/

theorem multigraph_truncation_adj_external {V E : Type*} (ends : E → Sym2 V) {u v : V} {e : E}
    (hu : u ∈ ends e) (hv : v ∈ ends e) (huv : u ≠ v) :
    (multigraph_truncation ends).Adj ⟨(u, e), hu⟩ ⟨(v, e), hv⟩ :=
  ⟨fun hp => huv (congrArg (fun x : {p : V × E // p.1 ∈ ends p.2} => x.1.1) hp), Or.inr rfl⟩
