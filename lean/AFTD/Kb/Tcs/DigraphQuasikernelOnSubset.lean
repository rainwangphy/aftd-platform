import AFTD.Prelude

/-!
# digraph_quasikernel_on_subset

Topic: graphs   Node: c385aeafd5b2

Provenance: helper lemma. Standard qualitative quasi-kernel existence construction, recalled in arXiv:2601.11847 Section 1.1; foundational helper for OP-337.

For any finite digraph and any finite vertex subset S there is an independent Q contained in S such that every vertex of S is reachable from Q in at most two arcs using intermediate vertices in S.
-/

theorem digraph_quasikernel_on_subset
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (S : Finset α) :
    ∃ Q : Finset α, Q ⊆ S ∧
      (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v ∈ S, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ w ∈ S, D.Adj u w ∧ D.Adj w v) := by
  classical
  induction S using Finset.strongInduction with
  | _ S ih =>
    by_cases he : S = ∅
    · subst S
      refine ⟨∅, ?_, ?_, ?_⟩ <;> simp
    · obtain ⟨v,hv⟩ := Finset.nonempty_iff_ne_empty.mpr he
      let T := S.filter (fun w => w ≠ v ∧ ¬ D.Adj v w)
      have hTS : T ⊆ S := Finset.filter_subset _ _
      have hT : T ⊂ S := by
        apply Finset.ssubset_iff_subset_ne.mpr
        refine ⟨hTS, ?_⟩
        intro eq
        have hvT : v ∈ T := by rw [eq]; exact hv
        exact ((Finset.mem_filter.mp hvT).2.1) rfl
      obtain ⟨Q,hQT,hind,hcover⟩ := ih T hT
      have hqprop : ∀ u ∈ Q, u ≠ v ∧ ¬ D.Adj v u := by
        intro u hu
        exact (Finset.mem_filter.mp (hQT hu)).2
      have coverT : ∀ x ∈ T, ∃ u ∈ Q,
          u = x ∨ D.Adj u x ∨ ∃ w ∈ S, D.Adj u w ∧ D.Adj w x := by
        intro x hx
        obtain ⟨u,hu,h⟩ := hcover x hx
        refine ⟨u,hu,?_⟩
        rcases h with heq | hsingle | ⟨w,hw,huw,hwx⟩
        · exact Or.inl heq
        · exact Or.inr (Or.inl hsingle)
        · exact Or.inr (Or.inr ⟨w,hTS hw,huw,hwx⟩)
      have outside : ∀ x ∈ S, x ∉ T → x = v ∨ D.Adj v x := by
        intro x hxS hxT
        by_cases hxv : x = v
        · exact Or.inl hxv
        · right
          by_contra hn
          exact hxT (Finset.mem_filter.mpr ⟨hxS,hxv,hn⟩)
      by_cases hex : ∃ u ∈ Q, D.Adj u v
      · refine ⟨Q,hQT.trans hTS,hind,?_⟩
        intro x hxS
        by_cases hxT : x ∈ T
        · exact coverT x hxT
        · obtain ⟨u,hu,huv⟩ := hex
          rcases outside x hxS hxT with hxv | hvx
          · subst x; exact ⟨u,hu,Or.inr (Or.inl huv)⟩
          · exact ⟨u,hu,Or.inr (Or.inr ⟨v,hv,huv,hvx⟩)⟩
      · refine ⟨insert v Q, ?_, ?_, ?_⟩
        · exact Finset.insert_subset hv (hQT.trans hTS)
        · intro a ha b hb hab
          rcases Finset.mem_insert.mp ha with haV | haQ
          · subst a
            rcases Finset.mem_insert.mp hb with hbV | hbQ
            · subst b; exact (hab rfl).elim
            · exact (hqprop b hbQ).2
          · rcases Finset.mem_insert.mp hb with hbV | hbQ
            · subst b; intro hav; exact hex ⟨a,haQ,hav⟩
            · exact hind a haQ b hbQ hab
        · intro x hxS
          by_cases hxT : x ∈ T
          · obtain ⟨u,hu,h⟩ := coverT x hxT
            exact ⟨u,Finset.mem_insert_of_mem hu,h⟩
          · rcases outside x hxS hxT with hxv | hvx
            · subst x; exact ⟨v,Finset.mem_insert_self _ _,Or.inl rfl⟩
            · exact ⟨v,Finset.mem_insert_self _ _,Or.inr (Or.inl hvx)⟩
