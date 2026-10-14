import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsKIndependent

/-!
# simple_graph_is_k_independent_mono

Topic: graphs   Node: 4a7522c4a568

Provenance: helper lemma. Monotonicity of k-independence, used in arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination) (Sec. 2 and Proposition 7.1).

Every subset of a k-independent vertex set is k-independent.
-/

theorem simple_graph_is_k_independent_mono {V : Type*} (G : SimpleGraph V) (k : ℕ)
    {I J : Finset V} (hIJ : I ⊆ J) (hJ : simple_graph_is_k_independent G k J) :
    simple_graph_is_k_independent G k I := open Finset in by
  intro v hv
  refine lt_of_le_of_lt (Set.ncard_le_ncard ?_ (J.finite_toSet.subset (fun w hw => hw.1)))
    (hJ v (hIJ hv))
  exact fun w hw => ⟨hIJ hw.1, hw.2⟩
