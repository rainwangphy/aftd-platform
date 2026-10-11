import AFTD.Prelude
import AFTD.Kb.Tcs.CardFilterSingletonProd
import AFTD.Kb.Tcs.CardFilterProdSingleton

/-!
# greedy_cut_finset_bound

Topic: approximation   Node: b0ca90c33a1c

Provenance: helper lemma. step towards greedy_max_cut_half_edges_lower_bound

For every finite set of vertices A in a simple graph G, there is a subset S ⊆ A such that the number of cut edges between S and A \ S is at least 1/4 of the ordered adjacent pairs in A × A.
-/

theorem greedy_cut_finset_bound_insert_left {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S T : Finset V) (hv : v ∉ S) :
    (((insert v S ×ˢ T).filter (fun ⟨u, w⟩ => G.Adj u w)).card) =
    (((S ×ˢ T).filter (fun ⟨u, w⟩ => G.Adj u w)).card) + (T.filter (fun w => G.Adj v w)).card := by
  rw [Finset.insert_eq, Finset.union_product, Finset.filter_union]
  have hd : Disjoint ({v} ×ˢ T) (S ×ˢ T) := by
    rw [Finset.disjoint_product]
    left
    exact Finset.disjoint_singleton_left.mpr hv
  have hdf : Disjoint (({v} ×ˢ T).filter (fun ⟨u, w⟩ => G.Adj u w)) ((S ×ˢ T).filter (fun ⟨u, w⟩ => G.Adj u w)) :=
    Finset.disjoint_filter_filter hd
  rw [Finset.card_union_of_disjoint hdf, card_filter_singleton_prod, add_comm]

theorem greedy_cut_finset_bound_insert_right {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (S T : Finset V) (hv : v ∉ T) :
    (((S ×ˢ insert v T).filter (fun ⟨u, w⟩ => G.Adj u w)).card) =
    (((S ×ˢ T).filter (fun ⟨u, w⟩ => G.Adj u w)).card) + (S.filter (fun w => G.Adj v w)).card := by
  rw [Finset.insert_eq, Finset.product_union, Finset.filter_union]
  have hd : Disjoint (S ×ˢ {v}) (S ×ˢ T) := by
    rw [Finset.disjoint_product]
    right
    exact Finset.disjoint_singleton_left.mpr hv
  have hdf : Disjoint ((S ×ˢ {v}).filter (fun ⟨u, w⟩ => G.Adj u w)) ((S ×ˢ T).filter (fun ⟨u, w⟩ => G.Adj u w)) :=
    Finset.disjoint_filter_filter hd
  rw [Finset.card_union_of_disjoint hdf, card_filter_prod_singleton, add_comm]

theorem greedy_cut_finset_bound_filter_insert {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (A : Finset V) :
    ((insert v A).filter (fun w => G.Adj v w)) = (A.filter (fun w => G.Adj v w)) := by
  ext w
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨rfl | hw, hadj⟩
    · exact (G.irrefl hadj).elim
    · exact ⟨hw, hadj⟩
  · rintro ⟨hw, hadj⟩
    exact ⟨Or.inr hw, hadj⟩

theorem greedy_cut_finset_bound_card_insert_insert {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (v : V) (A : Finset V) (hv : v ∉ A) :
    (((insert v A ×ˢ insert v A).filter (fun ⟨u, w⟩ => G.Adj u w)).card) =
    (((A ×ˢ A).filter (fun ⟨u, w⟩ => G.Adj u w)).card) + 2 * (A.filter (fun w => G.Adj v w)).card := by
  rw [greedy_cut_finset_bound_insert_left G v A (insert v A) hv]
  rw [greedy_cut_finset_bound_insert_right G v A A hv]
  rw [greedy_cut_finset_bound_filter_insert G v A]
  omega

theorem greedy_cut_finset_bound_filter_sdiff {V : Type*} [DecidableEq V]
    (p : V → Prop) [DecidablePred p] (A S : Finset V) (hS : S ⊆ A) :
    (A.filter p).card = (S.filter p).card + ((A \ S).filter p).card := by
  have hd : Disjoint S (A \ S) := Finset.disjoint_sdiff
  have hu : S ∪ (A \ S) = A := Finset.union_sdiff_of_subset hS
  nth_rw 1 [← hu]
  rw [Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hd)]

theorem greedy_cut_finset_bound_sdiff_insert_both {V : Type*} [DecidableEq V]
    (v : V) (A S : Finset V) (hv : v ∉ A) :
    (insert v A \ insert v S) = A \ S := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  aesop

theorem greedy_cut_finset_bound_sdiff_insert_left {V : Type*} [DecidableEq V]
    (v : V) (A S : Finset V) (hv : v ∉ S) :
    (insert v A \ S) = insert v (A \ S) := by
  ext x
  simp only [Finset.mem_sdiff, Finset.mem_insert]
  aesop

/-- Greedy cut bound on any subset: for any finite subset A, there is S ⊆ A such that the number of cut edges between S and A \ S is at least 1/4 of the ordered adjacent pairs in A × A. -/
theorem greedy_cut_finset_bound {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (A : Finset V) :
    ∃ S : Finset V, S ⊆ A ∧
      ((A ×ˢ A).filter (fun ⟨u, v⟩ => G.Adj u v)).card ≤
      4 * ((S ×ˢ (A \ S)).filter (fun ⟨u, v⟩ => G.Adj u v)).card := by
  induction' A using Finset.induction_on with v A hv ih
  · use ∅
    simp
  · rcases ih with ⟨S, hS, h_bound⟩
    have hvS : v ∉ S := fun h => hv (hS h)
    have hvAS : v ∉ A \ S := fun h => hv (Finset.mem_sdiff.mp h).1
    have h_split : (A.filter (fun w => G.Adj v w)).card =
        (S.filter (fun w => G.Adj v w)).card + ((A \ S).filter (fun w => G.Adj v w)).card :=
      greedy_cut_finset_bound_filter_sdiff (fun w => G.Adj v w) A S hS
    have h_card_A : (((insert v A ×ˢ insert v A).filter (fun ⟨u, w⟩ => G.Adj u w)).card) =
        (((A ×ˢ A).filter (fun ⟨u, w⟩ => G.Adj u w)).card) + 2 * (A.filter (fun w => G.Adj v w)).card :=
      greedy_cut_finset_bound_card_insert_insert G v A hv
    by_cases h_le : (S.filter (fun w => G.Adj v w)).card ≤ ((A \ S).filter (fun w => G.Adj v w)).card
    · use insert v S
      refine ⟨Finset.insert_subset_insert v hS, ?_⟩
      rw [greedy_cut_finset_bound_sdiff_insert_both v A S hv]
      rw [greedy_cut_finset_bound_insert_left G v S (A \ S) hvS]
      omega
    · use S
      refine ⟨hS.trans (Finset.subset_insert v A), ?_⟩
      rw [greedy_cut_finset_bound_sdiff_insert_left v A S hvS]
      rw [greedy_cut_finset_bound_insert_right G v S (A \ S) hvAS]
      omega
