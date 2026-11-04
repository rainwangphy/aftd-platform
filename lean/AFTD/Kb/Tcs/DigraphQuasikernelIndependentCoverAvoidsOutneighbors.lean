import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphQuasikernelOnSubset

/-!
# digraph_quasikernel_independent_cover_avoids_outneighbors

Topic: graphs   Node: 1c7b558c78fa

Provenance: helper lemma. Strengthened recursive independent-set construction, https://arxiv.org/html/2610.29659 Section 2.

In a finite loopless digraph, every independent set is contained in the closed out-neighborhood of a quasi-kernel that contains none of its open out-neighbors.
-/

theorem digraph_quasikernel_independent_cover_avoids_outneighbors {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (I : Finset α)
    (hind : ∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ D.Adj u v)
    (hloop : ∀ v, ¬ D.Adj v v) :
    ∃ Q : Finset α,
      (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) ∧
      (∀ i ∈ I, ∃ q ∈ Q, q = i ∨ D.Adj q i) ∧
      (∀ v ∈ Q, ¬ ∃ i ∈ I, D.Adj i v) := by
  classical
  let T := Finset.univ.filter fun x => x ∉ I ∧ ¬ ∃ i ∈ I, D.Adj i x
  obtain ⟨Q,hQT,hQind,hQcov⟩ := digraph_quasikernel_on_subset D T
  let R := I.filter fun i => ¬ ∃ q ∈ Q, D.Adj q i
  let P := Q ∪ R
  have hfirst : ∀ i ∈ I, ∃ q ∈ P, q = i ∨ D.Adj q i := by
    intro i hi
    by_cases h : ∃ q ∈ Q, D.Adj q i
    · obtain ⟨q,hq,hqi⟩ := h
      exact ⟨q,Finset.mem_union_left _ hq,Or.inr hqi⟩
    · have hiR : i ∈ R := Finset.mem_filter.mpr ⟨hi,h⟩
      exact ⟨i,Finset.mem_union_right _ hiR,Or.inl rfl⟩
  refine ⟨P, ?_, ?_, hfirst, ?_⟩
  · intro a ha b hb hab
    rcases Finset.mem_union.mp ha with ha | ha <;>
      rcases Finset.mem_union.mp hb with hb | hb
    · exact hQind a ha b hb hab
    · exact fun h => (Finset.mem_filter.mp hb).2 ⟨a,ha,h⟩
    · exact fun h => (Finset.mem_filter.mp (hQT hb)).2.2 ⟨a,(Finset.mem_filter.mp ha).1,h⟩
    · exact hind a (Finset.mem_filter.mp ha).1 b (Finset.mem_filter.mp hb).1 hab
  · intro v
    by_cases hvT : v ∈ T
    · obtain ⟨q,hq,h⟩ := hQcov v hvT
      refine ⟨q,Finset.mem_union_left _ hq,?_⟩
      rcases h with h | h | ⟨w,_,h1,h2⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨w,h1,h2⟩)
    · have houtside : v ∈ I ∨ ∃ i ∈ I, D.Adj i v := by
        by_contra hn
        apply hvT
        apply Finset.mem_filter.mpr
        constructor
        · exact Finset.mem_univ v
        · push_neg at hn
          exact ⟨hn.1, fun ⟨i,hi,hiv⟩ => hn.2 i hi hiv⟩
      rcases houtside with hi | ⟨i,hi,hiv⟩
      · obtain ⟨q,hq,h⟩ := hfirst v hi
        exact ⟨q,hq,h.elim Or.inl (fun h => Or.inr (Or.inl h))⟩
      · obtain ⟨q,hq,h⟩ := hfirst i hi
        rcases h with h | h
        · subst q
          exact ⟨i,hq,Or.inr (Or.inl hiv)⟩
        · exact ⟨q,hq,Or.inr (Or.inr ⟨i,h,hiv⟩)⟩

  · intro v hv ⟨i,hi,hiv⟩
    rcases Finset.mem_union.mp hv with hv | hv
    · exact (Finset.mem_filter.mp (hQT hv)).2.2 ⟨i,hi,hiv⟩
    · have hvI : v ∈ I := (Finset.mem_filter.mp hv).1
      by_cases h : i = v
      · subst i
        exact hloop v hiv
      · exact hind i hi v hvI h hiv
