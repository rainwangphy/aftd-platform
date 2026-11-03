import AFTD.Prelude
import AFTD.Kb.Tcs.MultigraphTruncation

/-!
# multigraph_truncation_not_adj

Topic: graphs   Node: ea451ed6a5ab

Provenance: helper lemma. sanity lemma for multigraph_truncation

Sanity: ports at different vertices and on different edges of G are not adjacent in the truncation.
-/

theorem multigraph_truncation_not_adj {V E : Type*} (ends : E → Sym2 V)
    (p q : {p : V × E // p.1 ∈ ends p.2}) (hv : p.1.1 ≠ q.1.1) (he : p.1.2 ≠ q.1.2) :
    ¬ (multigraph_truncation ends).Adj p q :=
  fun hadj => hadj.2.elim hv he
