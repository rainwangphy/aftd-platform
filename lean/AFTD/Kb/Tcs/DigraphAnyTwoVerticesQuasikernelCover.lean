import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphKernelPerfectSubsetQuasikernelCover

/-!
# digraph_any_two_vertices_quasikernel_cover

Topic: graphs   Node: 8e5ef11fcc99

Provenance: helper lemma. Two-vertex consequence of Lemma 14 of https://www.combinatorics.org/ojs/index.php/eljc/article/download/v32i2p53/pdf/, with arcs reversed.

For any two vertices of a finite digraph, some quasi-kernel has both vertices in its closed out-neighborhood.
-/

theorem digraph_any_two_vertices_quasikernel_cover
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] (a b : α) :
    ∃ Q : Finset α,
      (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v, ∃ u ∈ Q, u = v ∨ D.Adj u v ∨ ∃ z, D.Adj u z ∧ D.Adj z v) ∧
      (∃ u ∈ Q, u = a ∨ D.Adj u a) ∧
      (∃ u ∈ Q, u = b ∨ D.Adj u b) := by
  classical
  let S : Finset α := {a,b}
  have hker : ∀ T : Finset α, T ⊆ S → ∃ K : Finset α,
      K ⊆ T ∧
      (∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v ∈ T, ∃ u ∈ K, u = v ∨ D.Adj u v) := by
    intro T hT
    have hm : ∀ v ∈ T, v = a ∨ v = b := by
      intro v hv
      have hvS := hT hv
      simpa [S] using hvS
    have hsingle : ∀ x ∈ T, (∀ v ∈ T, x = v ∨ D.Adj x v) →
        ∃ K : Finset α, K ⊆ T ∧
          (∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v) ∧
          (∀ v ∈ T, ∃ u ∈ K, u = v ∨ D.Adj u v) := by
      intro x hx hdom
      refine ⟨{x}, ?_, ?_, ?_⟩
      · simpa using hx
      · intro u hu v hv huv
        simp only [Finset.mem_singleton] at hu hv
        subst u; subst v
        exact (huv rfl).elim
      · intro v hv
        exact ⟨x,by simp,hdom v hv⟩
    have hsub : ∀ x, T ⊆ {x} → ∃ K : Finset α, K ⊆ T ∧
        (∀ u ∈ K, ∀ v ∈ K, u ≠ v → ¬ D.Adj u v) ∧
        (∀ v ∈ T, ∃ u ∈ K, u = v ∨ D.Adj u v) := by
      intro x hTx
      refine ⟨T,Finset.Subset.rfl,?_,?_⟩
      · intro u hu v hv huv
        have hu' : u = x := Finset.mem_singleton.mp (hTx hu)
        have hv' : v = x := Finset.mem_singleton.mp (hTx hv)
        subst u; subst v
        exact (huv rfl).elim
      · intro v hv
        exact ⟨v,hv,Or.inl rfl⟩
    by_cases hab : D.Adj a b
    · by_cases ha : a ∈ T
      · apply hsingle a ha
        intro v hv
        rcases hm v hv with rfl | rfl
        · exact Or.inl rfl
        · exact Or.inr hab
      · apply hsub b
        intro v hv
        rcases hm v hv with rfl | rfl
        · exact (ha hv).elim
        · simp
    · by_cases hba : D.Adj b a
      · by_cases hb : b ∈ T
        · apply hsingle b hb
          intro v hv
          rcases hm v hv with rfl | rfl
          · exact Or.inr hba
          · exact Or.inl rfl
        · apply hsub a
          intro v hv
          rcases hm v hv with rfl | rfl
          · simp
          · exact (hb hv).elim
      · refine ⟨T,Finset.Subset.rfl,?_,?_⟩
        · intro u hu v hv huv hadj
          rcases hm u hu with rfl | rfl <;> rcases hm v hv with rfl | rfl
          · exact (huv rfl).elim
          · exact hab hadj
          · exact hba hadj
          · exact (huv rfl).elim
        · intro v hv
          exact ⟨v,hv,Or.inl rfl⟩
  obtain ⟨Q,hind,hcov,hfirst,_⟩ := digraph_kernel_perfect_subset_quasikernel_cover D S hker
  exact ⟨Q,hind,hcov,hfirst a (by simp [S]),hfirst b (by simp [S])⟩
