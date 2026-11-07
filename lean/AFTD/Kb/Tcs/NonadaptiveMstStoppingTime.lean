import AFTD.Prelude
import AFTD.Kb.Optimization.IsMstCertificate

/-!
# nonadaptive_mst_stopping_time

Topic: approximation   Node: fadc7f52220d

Provenance: formalization of a published result. Source: arXiv:2610.40844 Sec. 2.1, Lemma 2.2

Given a simple graph G, a querying order π : List G.edgeSet, and a realization α : G.edgeSet → Bool, the stopping time is the minimum number of queries k such that the partial realization revealing the first k edges of π certifies an MST of G.
-/

/-- The number of queries performed by querying edges in order π until an MST is certified under realization α. -/
noncomputable def nonadaptive_mst_stopping_time {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (π : List G.edgeSet) (α : G.edgeSet → Bool) : ℕ := sInf {k : ℕ | is_mst_certificate G (fun e => if e ∈ (π.take k).toFinset then some (α e) else none)}
