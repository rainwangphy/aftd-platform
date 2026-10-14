import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphIsKIndependent

/-!
# simple_graph_k_independent_is_k_independent_one_iff

Topic: graphs   Node: 3cf32e697efe

Provenance: helper lemma. Sanity lemma: β_1 = α, as noted in arXiv:2610.03785 (Upper k-star-forming sets, k-independence, and upper domination), Sec. 2 (1).

A vertex set is 1-independent exactly when it is independent: no two of its vertices are adjacent.
-/

theorem simple_graph_k_independent_is_k_independent_one_iff {V : Type*} (G : SimpleGraph V)
    (I : Finset V) :
    simple_graph_is_k_independent G 1 I ↔ ∀ u ∈ I, ∀ v ∈ I, ¬ G.Adj u v := by
  unfold simple_graph_is_k_independent
  have hfin : ∀ u, ({w | w ∈ I ∧ G.Adj u w} : Set V).Finite :=
    fun u => I.finite_toSet.subset (fun w hw => hw.1)
  constructor
  · intro h u hu v hv huv
    have := h u hu
    rw [Nat.lt_one_iff, Set.ncard_eq_zero (hfin u)] at this
    have hmem : v ∈ ({w | w ∈ I ∧ G.Adj u w} : Set V) := ⟨hv, huv⟩
    rw [this] at hmem
    exact hmem
  · intro h u hu
    rw [Nat.lt_one_iff, Set.ncard_eq_zero (hfin u), Set.eq_empty_iff_forall_notMem]
    exact fun v hv => h u hu v hv.1 hv.2
