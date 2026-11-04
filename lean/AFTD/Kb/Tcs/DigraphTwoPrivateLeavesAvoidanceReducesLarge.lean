import AFTD.Prelude

/-!
# digraph_two_private_leaves_avoidance_reduces_large

Topic: graphs   Node: 68640a6a3a86

Provenance: helper lemma. Two-private-leaf reduction tested in experiment 14018, motivated by https://arxiv.org/abs/2610.23487.

Attach two distinct private outgoing leaves to each vertex of a finite digraph. Source-freeness is preserved and the leaves form the unique maximum independent set. Any quasi-kernel meeting at most half of the second leaves projects to a quasi-kernel of the original graph whose closed out-neighborhood has at least half of the original vertices.
-/

def in528_two_leaf_augmentation {α : Type} (D : Digraph α) : Digraph (α × Fin 3) where
  Adj x y := (x.2 = 0 ∧ y.2 = 0 ∧ D.Adj x.1 y.1) ∨
    (x.2 = 0 ∧ y.2 ≠ 0 ∧ x.1 = y.1)

theorem digraph_two_private_leaves_avoidance_reduces_large
    {α : Type} [Fintype α] [DecidableEq α]
    (D : Digraph α) [DecidableRel D.Adj] :
    let F := in528_two_leaf_augmentation D
    let I : Finset (α × Fin 3) := Finset.univ.filter (fun x => x.2 ≠ 0)
    ((∀ v, ∃ u, D.Adj u v) → ∀ v, ∃ u, F.Adj u v) ∧
    (∀ T : Finset (α × Fin 3),
      (∀ u ∈ T, ∀ v ∈ T, u ≠ v → ¬ F.Adj u v) →
      T.card ≤ I.card ∧ (T.card = I.card → T = I)) ∧
    (∀ Q : Finset (α × Fin 3),
      (∀ u ∈ Q, ∀ v ∈ Q, u ≠ v → ¬ F.Adj u v) →
      (∀ v, ∃ u ∈ Q, u = v ∨ F.Adj u v ∨ ∃ w, F.Adj u w ∧ F.Adj w v) →
      2 * (Q.filter (fun x => x.2 = 2)).card ≤ Fintype.card α →
      let P : Finset α := Finset.univ.filter (fun u => (u, 0) ∈ Q)
      (∀ u ∈ P, ∀ v ∈ P, u ≠ v → ¬ D.Adj u v) ∧
      (∀ v, ∃ u ∈ P, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v) ∧
      Fintype.card α ≤ 2 * (Finset.univ.filter
        (fun v => ∃ u ∈ P, u = v ∨ D.Adj u v)).card) := by
  classical
  intro F I
  have h10 : (1 : Fin 3) ≠ 0 := by decide
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h12 : (1 : Fin 3) ≠ 2 := by decide
  refine ⟨?_, ?_, ?_⟩
  · intro hD ⟨v, i⟩
    by_cases hi : i = 0
    · obtain ⟨u, hu⟩ := hD v
      use (u, 0)
      subst hi
      left
      exact ⟨rfl, rfl, hu⟩
    · use (v, 0)
      right
      exact ⟨rfl, hi, rfl⟩
  · intro T hT
    let f : (α × Fin 3) → (α × Fin 3) := fun x => if x.2 = 0 then (x.1, 1) else x
    have hf_maps : Set.MapsTo f ↑T ↑I := by
      intro ⟨x1, x2⟩ _
      simp only [f, I, Finset.mem_coe, Finset.mem_filter, Finset.mem_univ, true_and]
      split_ifs with h
      · exact h10
      · exact h
    have hf_inj : Set.InjOn f ↑T := by
      intro ⟨u1, u2⟩ hu ⟨v1, v2⟩ hv heq
      dsimp [f] at heq
      split_ifs at heq with hu0 hv0 hv0
      · ext
        · injection heq with h1 _
        · rw [hu0, hv0]
      · injection heq with h1 h2
        have hu_adj : F.Adj (u1, u2) (v1, v2) := by
          dsimp [F, in528_two_leaf_augmentation]
          right
          refine ⟨hu0, ?_, h1⟩
          rw [← h2]
          exact h10
        have hne : (u1, u2) ≠ (v1, v2) := by
          intro h
          injection h with _ h_u2_eq_v2
          apply hv0
          rw [← h_u2_eq_v2, hu0]
        exact (hT (u1, u2) hu (v1, v2) hv hne hu_adj).elim
      · injection heq with h1 h2
        have hv_adj : F.Adj (v1, v2) (u1, u2) := by
          dsimp [F, in528_two_leaf_augmentation]
          right
          refine ⟨hv0, ?_, h1.symm⟩
          rw [h2]
          exact h10
        have hne : (v1, v2) ≠ (u1, u2) := by
          intro h
          injection h with _ h_v2_eq_u2
          apply hu0
          rw [← h_v2_eq_u2, hv0]
        exact (hT (v1, v2) hv (u1, u2) hu hne hv_adj).elim
      · exact heq
    have hle : T.card ≤ I.card := Finset.card_le_card_of_injOn f hf_maps hf_inj
    refine ⟨hle, fun h_eq => ?_⟩
    have hsurj := Finset.surjOn_of_injOn_of_card_le f hf_maps hf_inj (le_of_eq h_eq.symm)
    have h2_mem : ∀ a : α, (a, (2 : Fin 3)) ∈ T := by
      intro a
      have hy : (a, (2 : Fin 3)) ∈ I := by
        simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
        exact h20
      obtain ⟨⟨x1, x2⟩, hx, hfx⟩ := hsurj hy
      dsimp [f] at hfx
      split_ifs at hfx with hx0
      · injection hfx with _ hcontra
        exact (h12 hcontra).elim
      · rwa [← hfx]
    have h0_not_mem : ∀ a : α, (a, (0 : Fin 3)) ∉ T := by
      intro a ha0
      have ha2 := h2_mem a
      have hne : (a, (0 : Fin 3)) ≠ (a, (2 : Fin 3)) := by
        intro h
        injection h with _ h2
        revert h2
        decide
      have hadj : F.Adj (a, (0 : Fin 3)) (a, (2 : Fin 3)) := by
        dsimp [F, in528_two_leaf_augmentation]
        right
        exact ⟨rfl, h20, rfl⟩
      exact hT (a, 0) ha0 (a, 2) ha2 hne hadj
    have hsub : T ⊆ I := by
      intro ⟨x1, x2⟩ hx
      simp only [I, Finset.mem_filter, Finset.mem_univ, true_and]
      intro hx0
      have : (x1, x2) = (x1, (0 : Fin 3)) := Prod.ext rfl hx0
      rw [this] at hx
      exact h0_not_mem x1 hx
    exact Finset.eq_of_subset_of_card_le hsub (le_of_eq h_eq.symm)
  · intro Q hQ_ind hQ_qk hQ_small P
    have hP_ind : ∀ u ∈ P, ∀ v ∈ P, u ≠ v → ¬ D.Adj u v := by
      intro u hu v hv hne hadj
      simp only [P, Finset.mem_filter, Finset.mem_univ, true_and] at hu hv
      have hne' : (u, (0 : Fin 3)) ≠ (v, 0) := by
        intro h
        injection h with h1 _
        exact hne h1
      have hadj' : F.Adj (u, 0) (v, 0) := by
        dsimp [F, in528_two_leaf_augmentation]
        left
        exact ⟨rfl, rfl, hadj⟩
      exact hQ_ind (u, 0) hu (v, 0) hv hne' hadj'
    have hP_qk : ∀ v, ∃ u ∈ P, u = v ∨ D.Adj u v ∨ ∃ w, D.Adj u w ∧ D.Adj w v := by
      intro v
      obtain ⟨u, huQ, hu_reach⟩ := hQ_qk (v, 0)
      rcases hu_reach with rfl | hadj | ⟨w, hw1, hw2⟩
      · use v
        refine ⟨by simp [P, huQ], Or.inl rfl⟩
      · dsimp [F, in528_two_leaf_augmentation] at hadj
        rcases hadj with ⟨hu0, hv0, hadjD⟩ | ⟨hu0, hv0, heq1⟩
        · use u.1
          have huP : u.1 ∈ P := by
            simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
            have : u = (u.1, 0) := Prod.ext rfl hu0
            rwa [this] at huQ
          exact ⟨huP, Or.inr (Or.inl hadjD)⟩
        · contradiction
      · dsimp [F, in528_two_leaf_augmentation] at hw1 hw2
        rcases hw2 with ⟨hw0, hv0, hw2D⟩ | ⟨hw0, hv0, -⟩
        · rcases hw1 with ⟨hu0, -, hw1D⟩ | ⟨hu0, hw_ne, -⟩
          · use u.1
            have huP : u.1 ∈ P := by
              simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
              have : u = (u.1, 0) := Prod.ext rfl hu0
              rwa [this] at huQ
            exact ⟨huP, Or.inr (Or.inr ⟨w.1, hw1D, hw2D⟩)⟩
          · exact (hw_ne hw0).elim
        · contradiction
    refine ⟨hP_ind, hP_qk, ?_⟩
    let N := Finset.univ.filter (fun v => ∃ u ∈ P, u = v ∨ D.Adj u v)
    have hN_mem : ∀ v ∈ Finset.univ \ N, (v, (2 : Fin 3)) ∈ Q.filter (fun x => x.2 = 2) := by
      intro v hv
      rw [Finset.mem_sdiff] at hv
      have hvN : v ∉ N := hv.2
      simp only [N, Finset.mem_filter, Finset.mem_univ, true_and, not_exists] at hvN
      obtain ⟨u, huQ, hu_reach⟩ := hQ_qk (v, 2)
      have hu_eq : u = (v, 2) := by
        rcases hu_reach with heq | hadj | ⟨w, hw1, hw2⟩
        · exact heq
        · dsimp [F, in528_two_leaf_augmentation] at hadj
          rcases hadj with ⟨-, hcontra, -⟩ | ⟨hu0, -, heq1⟩
          · exact (h20 hcontra).elim
          · have huP : v ∈ P := by
              simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
              have : u = (v, 0) := Prod.ext heq1 hu0
              rwa [this] at huQ
            exact (hvN v ⟨huP, Or.inl rfl⟩).elim
        · dsimp [F, in528_two_leaf_augmentation] at hw1 hw2
          rcases hw2 with ⟨-, hcontra, -⟩ | ⟨hw0, -, heq_w⟩
          · exact (h20 hcontra).elim
          · rcases hw1 with ⟨hu0, -, hadj1⟩ | ⟨hu0, hw_ne, -⟩
            · have huP : u.1 ∈ P := by
                simp only [P, Finset.mem_filter, Finset.mem_univ, true_and]
                have : u = (u.1, 0) := Prod.ext rfl hu0
                rwa [this] at huQ
              rw [heq_w] at hadj1
              exact (hvN u.1 ⟨huP, Or.inr hadj1⟩).elim
            · exact (hw_ne hw0).elim
      exact Finset.mem_filter.mpr ⟨hu_eq ▸ huQ, rfl⟩
    have h_maps : Set.MapsTo (fun (v : α) => (v, (2 : Fin 3))) (↑(Finset.univ \ N) : Set α)
        (↑(Q.filter (fun x => x.2 = 2)) : Set (α × Fin 3)) := by
      intro v hv
      exact hN_mem v (Finset.mem_coe.mp hv)
    have h_inj : Set.InjOn (fun (v : α) => (v, (2 : Fin 3))) (↑(Finset.univ \ N) : Set α) := by
      intro u _ v _ heq
      exact (Prod.mk.injEq u 2 v 2).mp heq |>.1
    have h_card_le := Finset.card_le_card_of_injOn _ h_maps h_inj
    have h_sdiff : (Finset.univ \ N).card = Fintype.card α - N.card := by
      rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ]
    have hN_le : N.card ≤ Fintype.card α := Finset.card_le_univ N
    change Fintype.card α ≤ 2 * N.card
    omega
