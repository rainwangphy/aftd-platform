import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphStarForestAdjIff
import AFTD.Kb.Tcs.SimpleGraphStarForest

/-!
# simple_graph_star_forest_edgeSet_ncard

Topic: graphs   Node: a6526c0e0127

Provenance: helper lemma. helper for arXiv:2610.25958 (Size Ramsey numbers of star forests with two components on one side), Lemma 2.3 (PR-280)

The star forest K_{1,n_1} ⊔ ... ⊔ K_{1,n_q} has ∑ n_i edges.
-/

theorem simple_graph_star_forest_edgeSet_ncard (q : ℕ) (n : Fin q → ℕ) :
    (simple_graph_star_forest q n).edgeSet.ncard = ∑ i, n i := by
  let φ : (Σ i : Fin q, Fin (n i)) → Sym2 (Σ i : Fin q, Option (Fin (n i))) :=
    fun x => s(⟨x.1, none⟩, ⟨x.1, some x.2⟩)
  have hφ : Function.Injective φ := by
    rintro ⟨i, j⟩ ⟨i', j'⟩ h
    simp only [φ, Sym2.eq_iff] at h
    rcases h with ⟨_, h2⟩ | ⟨h1, _⟩
    · simp only [Sigma.mk.inj_iff] at h2
      obtain ⟨rfl, h⟩ := h2
      simp only [heq_eq_eq, Option.some.injEq] at h
      rw [h]
    · exact absurd (congrArg (fun x : (Σ i : Fin q, Option (Fin (n i))) => x.2.isSome) h1) (by simp)
  have hrange : (simple_graph_star_forest q n).edgeSet = Set.range φ := by
    ext e
    induction e using Sym2.ind with
    | h u v =>
      rcases u with ⟨i, a⟩
      rcases v with ⟨i', b⟩
      rw [SimpleGraph.mem_edgeSet, simple_graph_star_forest_adj_iff, Set.mem_range]
      constructor
      · rintro ⟨hi, h⟩
        simp only at hi
        subst hi
        rcases h with ⟨ha, hb⟩ | ⟨ha, hb⟩
        · simp only at ha hb
          subst ha
          obtain ⟨b, rfl⟩ := Option.ne_none_iff_exists'.mp hb
          exact ⟨⟨i, b⟩, rfl⟩
        · simp only at ha hb
          subst hb
          obtain ⟨a, rfl⟩ := Option.ne_none_iff_exists'.mp ha
          exact ⟨⟨i, a⟩, Sym2.eq_swap⟩
      · rintro ⟨⟨j, c⟩, h⟩
        simp only [φ, Sym2.eq_iff] at h
        rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · cases h1
          cases h2
          exact ⟨rfl, Or.inl ⟨rfl, by simp⟩⟩
        · cases h1
          cases h2
          exact ⟨rfl, Or.inr ⟨by simp, rfl⟩⟩
  rw [hrange, Set.ncard_range_of_injective hφ, Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp
