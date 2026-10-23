import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStarForestEdgeSetNcard
import AFTD.Kb.Tcs.CompleteBipartiteOneIsContainedOfAdj
import AFTD.Kb.Tcs.SimpleGraphStarForest
import AFTD.Kb.Tcs.SimpleGraphSizeRamseyArrows

/-!
# simple_graph_size_ramsey_star_star_forest_arrows

Topic: graphs   Node: 8e3a14a1d54b

Provenance: helper lemma. upper bound in the proof of arXiv:2610.25958 (Size Ramsey numbers of star forests with two components on one side), Lemma 2.3 (PR-280)

Upper bound of Lemma 2.3 of arXiv:2610.25958. Some finite graph with ∑_i (p + n_i - 1) edges arrows (K_{1,p}, ⊔_i K_{1,n_i}): the disjoint union of the stars K_{1,p+n_i-1}.
-/

theorem simple_graph_size_ramsey_star_star_forest_arrows (p q : ℕ) (hp : 0 < p) (n : Fin q → ℕ)
    (hn : ∀ i, 0 < n i) :
    ∃ (k : ℕ) (G : SimpleGraph (Fin k)), G.edgeSet.ncard = ∑ i, (p + n i - 1) ∧
      simple_graph_size_ramsey_arrows G (completeBipartiteGraph (Fin 1) (Fin p))
        (simple_graph_star_forest q n) := by
  classical
  let m : Fin q → ℕ := fun i => p + n i - 1
  let e := Fintype.equivFin (Σ i : Fin q, Option (Fin (m i)))
  let S := simple_graph_star_forest q m
  refine ⟨_, S.map e.toEmbedding, ?_, ?_⟩
  · rw [SimpleGraph.edgeSet_map, Set.ncard_image_of_injective _ e.toEmbedding.sym2Map.injective]
    exact simple_graph_star_forest_edgeSet_ncard q m
  intro R _
  have hGadj : ∀ a b, (S.map e.toEmbedding).Adj (e a) (e b) ↔ S.Adj a b := by
    intro a b
    rw [SimpleGraph.map_adj]
    constructor
    · rintro ⟨a', b', h, ha, hb⟩
      simp only [Equiv.coe_toEmbedding, EmbeddingLike.apply_eq_iff_eq] at ha hb
      subst ha hb
      exact h
    · intro h
      exact ⟨a, b, h, rfl, rfl⟩
  let red : ∀ i, Finset (Fin (m i)) := fun i =>
    Finset.univ.filter (fun j => R.Adj (e ⟨i, none⟩) (e ⟨i, some j⟩))
  by_cases hc : ∃ i, p ≤ (red i).card
  · obtain ⟨i, hi⟩ := hc
    left
    refine complete_bipartite_one_isContained_of_adj R p (e ⟨i, none⟩)
      (fun j => e ⟨i, some ((red i).orderEmbOfFin rfl (Fin.castLE hi j))⟩) ?_ (fun j => ?_)
    · intro a b h
      have h := e.injective h
      simp only [Sigma.mk.inj_iff, heq_eq_eq, true_and, Option.some.injEq] at h
      exact Fin.castLE_injective hi (((red i).orderEmbOfFin rfl).injective h)
    · have := (red i).orderEmbOfFin_mem rfl (Fin.castLE hi j)
      simp only [red, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
  · push Not at hc
    right
    let blue : ∀ i, Finset (Fin (m i)) := fun i =>
      Finset.univ.filter (fun j => ¬ R.Adj (e ⟨i, none⟩) (e ⟨i, some j⟩))
    have hb : ∀ i, n i ≤ (blue i).card := by
      intro i
      have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin (m i))))
        (fun j => R.Adj (e ⟨i, none⟩) (e ⟨i, some j⟩))
      rw [Finset.card_univ, Fintype.card_fin] at h1
      have h2 := hc i
      have h3 := hn i
      have h4 : m i = p + n i - 1 := rfl
      simp only [red] at h2
      simp only [blue]
      omega
    let b : ∀ i, Fin (n i) → Fin (m i) := fun i j => (blue i).orderEmbOfFin rfl (Fin.castLE (hb i) j)
    have hbinj : ∀ i, Function.Injective (b i) := fun i =>
      ((blue i).orderEmbOfFin rfl).injective.comp (Fin.castLE_injective (hb i))
    have hbmem : ∀ i j, ¬ R.Adj (e ⟨i, none⟩) (e ⟨i, some (b i j)⟩) := by
      intro i j
      have := (blue i).orderEmbOfFin_mem rfl (Fin.castLE (hb i) j)
      simp only [blue, Finset.mem_filter, Finset.mem_univ, true_and] at this
      exact this
    let ψ : (Σ i : Fin q, Option (Fin (n i))) → Fin (Fintype.card (Σ i : Fin q, Option (Fin (m i)))) :=
      fun x => e ⟨x.1, x.2.map (b x.1)⟩
    refine ⟨⟨⟨ψ, ?_⟩, ?_⟩⟩
    · rintro ⟨i, a⟩ ⟨i', c⟩ ⟨hii, h⟩
      simp only at hii
      subst hii
      rw [SimpleGraph.sdiff_adj]
      rcases h with ⟨ha, hc'⟩ | ⟨ha, hc'⟩
      · simp only at ha hc'
        subst ha
        obtain ⟨c, rfl⟩ := Option.ne_none_iff_exists'.mp hc'
        exact ⟨(hGadj _ _).2 ⟨rfl, Or.inl ⟨rfl, by simp⟩⟩, hbmem i c⟩
      · simp only at ha hc'
        subst hc'
        obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.mp ha
        exact ⟨(hGadj _ _).2 ⟨rfl, Or.inr ⟨by simp, rfl⟩⟩, fun h => hbmem i a h.symm⟩
    · rintro ⟨i, a⟩ ⟨i', c⟩ h
      have h := e.injective h
      simp only [Sigma.mk.inj_iff] at h ⊢
      obtain ⟨rfl, h⟩ := h
      refine ⟨rfl, ?_⟩
      rw [heq_eq_eq] at h ⊢
      exact Option.map_injective (hbinj i) h
