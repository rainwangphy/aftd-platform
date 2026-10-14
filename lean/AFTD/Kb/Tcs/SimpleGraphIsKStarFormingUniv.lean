import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsKStarForming

/-!
# simple_graph_is_k_star_forming_univ

Topic: graphs   Node: fe4b70f1b2c3

Provenance: helper lemma. Sanity lemma for the definition of k-star-forming sets, arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination).

In a finite graph the whole vertex set is k-star-forming, for every k (there is no vertex outside it).
-/

theorem simple_graph_is_k_star_forming_univ {V : Type*} [Fintype V] (G : SimpleGraph V) (k : ℕ) :
    simple_graph_is_k_star_forming G k Finset.univ := by
  intro v hv; exact absurd (Finset.mem_univ v) hv
