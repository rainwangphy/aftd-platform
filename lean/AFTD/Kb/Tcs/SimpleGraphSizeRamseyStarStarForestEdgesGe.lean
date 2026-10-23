import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStarForestEdgeSetNcard
import AFTD.Kb.Tcs.CompleteBipartiteOneIsContainedOfAdj
import AFTD.Kb.Tcs.ExistsAdjOfCompleteBipartiteOneIsContained
import AFTD.Kb.Tcs.SimpleGraphStarForestAdjCentreLeaf
import AFTD.Kb.Tcs.SimpleGraphStarForest
import AFTD.Kb.Tcs.SimpleGraphSizeRamseyArrows

/-!
# simple_graph_size_ramsey_star_star_forest_edges_ge

Topic: graphs   Node: 39a33cf2716e

Provenance: helper lemma. lower bound in the proof of arXiv:2610.25958 (Size Ramsey numbers of star forests with two components on one side), Lemma 2.3 (PR-280)

Lower bound of Lemma 2.3 of arXiv:2610.25958. Every finite graph G with G → (K_{1,p}, ⊔_i K_{1,n_i}) has at least ∑_i (p + n_i - 1) edges.
-/

theorem simple_graph_size_ramsey_star_star_forest_edges_ge (p q : ℕ) (hp : 0 < p) (n : Fin q → ℕ)
    (hn : ∀ i, 0 < n i) (k : ℕ) (G : SimpleGraph (Fin k))
    (hG : simple_graph_size_ramsey_arrows G (completeBipartiteGraph (Fin 1) (Fin p))
      (simple_graph_star_forest q n)) :
    ∑ i, (p + n i - 1) ≤ G.edgeSet.ncard := by
  classical
  obtain ⟨r, rfl⟩ : ∃ r, p = r + 1 := ⟨p - 1, by omega⟩
  clear hp
  induction r generalizing G with
  | zero =>
    rcases hG ⊥ bot_le with h | h
    · obtain ⟨v, g, -, hg⟩ := exists_adj_of_complete_bipartite_one_isContained _ _ h
      exact absurd (hg 0) (by simp)
    · rw [sdiff_bot] at h
      obtain ⟨f⟩ := h
      have h1 : (simple_graph_star_forest q n).edgeSet.ncard ≤ G.edgeSet.ncard := by
        have := Nat.card_le_card_of_injective f.mapEdgeSet f.mapEdgeSet.injective
        rwa [Nat.card_coe_set_eq, Nat.card_coe_set_eq] at this
      rw [simple_graph_star_forest_edgeSet_ncard] at h1
      simpa using h1
  | succ r ih =>
    rcases hG ⊥ bot_le with h | h
    · obtain ⟨v, g, -, hg⟩ := exists_adj_of_complete_bipartite_one_isContained _ _ h
      exact absurd (hg 0) (by simp)
    rw [sdiff_bot] at h
    obtain ⟨f⟩ := h
    let c : Fin q → Fin k := fun i => f ⟨i, none⟩
    let l : Fin q → Fin k := fun i => f ⟨i, some ⟨0, hn i⟩⟩
    have hcl : ∀ i j, c i ≠ l j := by
      intro i j h
      have := congrArg (fun x : (Σ i : Fin q, Option (Fin (n i))) => x.2.isSome) (f.injective h)
      simp at this
    have hcc : ∀ i j, c i = c j → i = j := fun i j h => congrArg Sigma.fst (f.injective h)
    have hll : ∀ i j, l i = l j → i = j := fun i j h => congrArg Sigma.fst (f.injective h)
    let M : SimpleGraph (Fin k) := SimpleGraph.fromRel (fun x y => ∃ i, x = c i ∧ y = l i)
    have hMadj : ∀ i, M.Adj (c i) (l i) := fun i => by
      simp only [M, SimpleGraph.fromRel_adj]
      exact ⟨hcl i i, Or.inl ⟨i, rfl, rfl⟩⟩
    have hGcl : ∀ i, G.Adj (c i) (l i) := fun i =>
      f.toHom.map_adj (simple_graph_star_forest_adj_centre_leaf q n i ⟨0, hn i⟩)
    have hMG : M ≤ G := by
      intro x y h
      simp only [M, SimpleGraph.fromRel_adj] at h
      obtain ⟨-, ⟨i, rfl, rfl⟩ | ⟨i, rfl, rfl⟩⟩ := h
      · exact hGcl i
      · exact (hGcl i).symm
    have hmatch : ∀ v a b, M.Adj v a → M.Adj v b → a = b := by
      intro v a b ha hb
      simp only [M, SimpleGraph.fromRel_adj] at ha hb
      obtain ⟨-, ⟨i, hv, ha⟩ | ⟨i, ha, hv⟩⟩ := ha <;>
      obtain ⟨-, ⟨j, hv', hb⟩ | ⟨j, hb, hv'⟩⟩ := hb
      · rw [ha, hb, hcc i j (hv.symm.trans hv')]
      · exact absurd (hv.symm.trans hv') (hcl i j)
      · exact absurd (hv'.symm.trans hv) (hcl j i)
      · rw [ha, hb, hll i j (hv.symm.trans hv')]
    have hMq : q ≤ M.edgeSet.ncard := by
      have hinj : Function.Injective
          (fun i : Fin q => (⟨s(c i, l i), (SimpleGraph.mem_edgeSet _).2 (hMadj i)⟩ : M.edgeSet)) := by
        intro i j h
        simp only [Subtype.mk.injEq, Sym2.eq_iff] at h
        rcases h with ⟨h, -⟩ | ⟨h, -⟩
        · exact hcc i j h
        · exact absurd h (hcl i j)
      have := Nat.card_le_card_of_injective _ hinj
      rwa [Nat.card_eq_fintype_card, Fintype.card_fin, Nat.card_coe_set_eq] at this
    have hG' : simple_graph_size_ramsey_arrows (G \ M) (completeBipartiteGraph (Fin 1) (Fin (r + 1)))
        (simple_graph_star_forest q n) := by
      intro R' hR'
      have hle : R' ⊔ M ≤ G := sup_le (hR'.trans sdiff_le) hMG
      rcases hG (R' ⊔ M) hle with h | h
      · left
        obtain ⟨v, g, hginj, hg⟩ := exists_adj_of_complete_bipartite_one_isContained _ _ h
        by_cases hall : ∀ j, R'.Adj v (g j)
        · exact complete_bipartite_one_isContained_of_adj R' (r + 1) v (g ∘ Fin.castSucc)
            (hginj.comp (Fin.castSucc_injective _)) (fun j => hall _)
        · push Not at hall
          obtain ⟨j0, hj0⟩ := hall
          have hM0 : M.Adj v (g j0) := ((SimpleGraph.sup_adj _ _ _ _).1 (hg j0)).resolve_left hj0
          refine complete_bipartite_one_isContained_of_adj R' (r + 1) v (g ∘ j0.succAbove)
            (hginj.comp Fin.succAbove_right_injective) (fun j => ?_)
          rcases (SimpleGraph.sup_adj _ _ _ _).1 (hg (j0.succAbove j)) with h1 | h1
          · exact h1
          · exact absurd (hginj (hmatch v _ _ h1 hM0)) (Fin.succAbove_ne j0 j)
      · right
        rw [sdiff_sdiff_left, sup_comm]
        exact h
    have hih := ih (G \ M) hG'
    have hcount : G.edgeSet.ncard = (G \ M).edgeSet.ncard + M.edgeSet.ncard := by
      rw [SimpleGraph.edgeSet_sdiff, Set.ncard_sdiff_add_ncard_of_subset (SimpleGraph.edgeSet_mono hMG)]
    have hsum : ∑ i, (r + 1 + 1 + n i - 1) = ∑ i, (r + 1 + n i - 1) + q := by
      have : ∑ i, (r + 1 + 1 + n i - 1) = ∑ i, ((r + 1 + n i - 1) + 1) :=
        Finset.sum_congr rfl (fun i _ => by have := hn i; omega)
      rw [this, Finset.sum_add_distrib]
      simp
    omega
