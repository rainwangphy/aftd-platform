import AFTD.Prelude

/-!
# digraph_quasikernel_neighborhood_preserving_completion

Topic: graphs   Node: 0a8c500ed01a

Provenance: helper lemma. arXiv:2610.23487, Section 2, and OP-337 campaign; finite neighborhood-preserving completion.

A subset that preserves every first out-neighbor of a quasi-kernel can be uniquely completed to the least quasi-kernel lying between it and the original set; every vertex outside the original set is already two-step reached by that subset.
-/

theorem digraph_quasikernel_neighborhood_preserving_completion
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (K R : Finset α)
    (hRK : R ⊆ K)
    (hind : ∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v)
    (hcover : ∀ v, ∃ u ∈ K, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v)
    (hpres : ∀ v, (∃ u ∈ K, D.Adj u v) → ∃ u ∈ R, D.Adj u v) :
    ∃ P : Finset α, R ⊆ P ∧ P ⊆ K ∧
      (∀ u ∈ P, ∀ v ∈ P, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v, ∃ u ∈ P, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) ∧
      (∀ v, v ∉ K → ∃ u ∈ R, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) ∧
      (∀ P' : Finset α, R ⊆ P' → P' ⊆ K →
        (∀ v, ∃ u ∈ P', u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) → P ⊆ P') := by
  classical
  have houtside : ∀ v, v ∉ K → ∃ u ∈ R,
      u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v := by
    intro v hv
    obtain ⟨u,hu,h⟩ := hcover v
    rcases h with heq | hadj | ⟨w,huw,hwv⟩
    · subst u; exact (hv hu).elim
    · obtain ⟨r,hr,hrv⟩ := hpres v ⟨u,hu,hadj⟩
      exact ⟨r,hr,Or.inr (Or.inl hrv)⟩
    · obtain ⟨r,hr,hrw⟩ := hpres w ⟨u,hu,huw⟩
      exact ⟨r,hr,Or.inr (Or.inr ⟨w,hrw,hwv⟩)⟩
  let Z := Finset.univ.filter fun v => ¬ ∃ u ∈ R,
      u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v
  have hZK : Z ⊆ K := by
    intro z hz
    by_contra hzK
    exact (Finset.mem_filter.mp hz).2 (houtside z hzK)
  refine ⟨R ∪ Z, Finset.subset_union_left, Finset.union_subset hRK hZK, ?_, ?_, houtside, ?_⟩
  · intro u hu v hv huv
    have huK : u ∈ K := (Finset.union_subset hRK hZK) hu
    have hvK : v ∈ K := (Finset.union_subset hRK hZK) hv
    exact hind u huK v hvK huv
  · intro v
    by_cases hv : v ∈ Z
    · exact ⟨v,Finset.mem_union_right _ hv,Or.inl rfl⟩
    · have hv' : ¬ ¬ (∃ u ∈ R, u = v ∨ D.Adj u v ∨
          ∃ w, D.Adj u w ∧ D.Adj w v) := by
        intro hn
        exact hv (Finset.mem_filter.mpr ⟨Finset.mem_univ v,hn⟩)
      obtain ⟨u,hu,huv⟩ := Classical.not_not.mp hv'
      exact ⟨u,Finset.mem_union_left _ hu,huv⟩

  · intro P' hRP hPK hdom z hz
    rcases Finset.mem_union.mp hz with hzR | hzZ
    · exact hRP hzR
    · obtain ⟨u,hu,h⟩ := hdom z
      rcases h with heq | hadj | ⟨w,huw,hwz⟩
      · subst u; exact hu
      · obtain ⟨r,hr,hrz⟩ := hpres z ⟨u,hPK hu,hadj⟩
        exact ((Finset.mem_filter.mp hzZ).2 ⟨r,hr,Or.inr (Or.inl hrz)⟩).elim
      · obtain ⟨r,hr,hrw⟩ := hpres w ⟨u,hPK hu,huw⟩
        exact ((Finset.mem_filter.mp hzZ).2 ⟨r,hr,Or.inr (Or.inr ⟨w,hrw,hwz⟩)⟩).elim
