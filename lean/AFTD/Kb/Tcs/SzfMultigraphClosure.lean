import AFTD.Prelude
import AFTD.Kb.Tcs.SzfMultiForced

/-!
# szf_multigraph_closure

Topic: graphs   Node: 8f11473ade49

Provenance: formalization of a published result. Source: arXiv:2611.15741 Section 1 (SZF closure scl_G(S))

The skew zero forcing closure scl(S) of a vertex set S in the multigraph with adjacency multiplicities μ: the set of vertices forced from S under the multigraph skew colour change rule.
-/

/-- The skew zero forcing closure in a multigraph with multiplicities `μ`. -/
def szf_multigraph_closure {V : Type*} (μ : V → V → ℕ) (S : Set V) : Set V := {v | SzfMultiForced μ S v}
