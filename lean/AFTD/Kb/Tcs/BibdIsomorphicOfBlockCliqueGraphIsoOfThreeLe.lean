import AFTD.Prelude
import AFTD.Kb.Tcs.BibdBlockCliqueGraph
import AFTD.Kb.Tcs.BibdIsomorphic
import AFTD.Kb.Tcs.BIBD
import AFTD.Kb.Tcs.G

/-!
# bibd_isomorphic_of_block_clique_graph_iso_of_three_le

Topic: graphs   Node: 9d424d8c18b8

Provenance: original. Related work: arXiv:2611.05762, Conjecture 6.30.1 (Sec. 6.30, Algebraic Recoverability), for the construction of Sec. 6.9. The paper leaves this as a conjecture for a suitably restricted class; here the class is block size at least 3.

Recoverability of a BIBD from its modified block-clique graph when the block size k is at least 3: if two BIBDs D₁, D₂ with the same parameters (v, b, r, k, λ), k ≥ 3, have isomorphic block-clique graphs (bibd_block_clique_graph), then the designs are isomorphic (bibd_isomorphic).
-/

theorem bibd_block_clique_graph_point_no_triangle {X B : Type*} {v b r k lam : ℕ}
    (D : BIBD X B v b r k lam) (x : X) (a c : X ⊕ (B × Fin k))
    (h1 : (bibd_block_clique_graph D).Adj (Sum.inl x) a)
    (h2 : (bibd_block_clique_graph D).Adj (Sum.inl x) c)
    (h3 : (bibd_block_clique_graph D).Adj a c) : False := by
  rcases a with y | ⟨b1, j1⟩
  · simp [bibd_block_clique_graph] at h1
  rcases c with y | ⟨b2, j2⟩
  · simp [bibd_block_clique_graph] at h2
  simp only [bibd_block_clique_graph] at h1 h2 h3
  obtain ⟨rfl, hne⟩ := h3
  exact hne (D.block_inj _ (h1.trans h2.symm))

theorem bibd_block_clique_graph_local_triangle {X B : Type*} {v b r k lam : ℕ}
    (D : BIBD X B v b r k lam) (hk : 3 ≤ k) (β : B) (j : Fin k) :
    ∃ a c : X ⊕ (B × Fin k), (bibd_block_clique_graph D).Adj (Sum.inr (β, j)) a ∧
      (bibd_block_clique_graph D).Adj (Sum.inr (β, j)) c ∧
      (bibd_block_clique_graph D).Adj a c := by
  obtain ⟨j1, j2, h1, h2, h3⟩ : ∃ j1 j2 : Fin k, j ≠ j1 ∧ j ≠ j2 ∧ j1 ≠ j2 := by
    have hc : 2 < (Finset.univ.erase j : Finset (Fin k)).card + 1 := by
      simp [Finset.card_erase_of_mem]; omega
    have hc' : 1 < (Finset.univ.erase j : Finset (Fin k)).card := by omega
    obtain ⟨p, hp, q, hq, hpq⟩ := Finset.one_lt_card.mp hc'
    exact ⟨p, q, (Finset.ne_of_mem_erase hp).symm, (Finset.ne_of_mem_erase hq).symm, hpq⟩
  refine ⟨Sum.inr (β, j1), Sum.inr (β, j2), ?_, ?_, ?_⟩
  · simpa [bibd_block_clique_graph] using h1
  · simpa [bibd_block_clique_graph] using h2
  · simpa [bibd_block_clique_graph] using h3

theorem bibd_block_clique_graph_iso_point {X₁ B₁ X₂ B₂ : Type*} {v b r k lam : ℕ}
    (D₁ : BIBD X₁ B₁ v b r k lam) (D₂ : BIBD X₂ B₂ v b r k lam) (hk : 3 ≤ k)
    (φ : bibd_block_clique_graph D₁ ≃g bibd_block_clique_graph D₂) (x : X₁) :
    ∃ y, φ (Sum.inl x) = Sum.inl y := by
  rcases h : φ (Sum.inl x) with y | ⟨β, j⟩
  · exact ⟨y, rfl⟩
  · exfalso
    obtain ⟨a, c, h1, h2, h3⟩ := bibd_block_clique_graph_local_triangle D₂ hk β j
    rw [← h] at h1 h2
    exact bibd_block_clique_graph_point_no_triangle D₁ x (φ.symm a) (φ.symm c)
      (by have t := φ.symm.map_rel_iff.2 h1; rwa [RelIso.symm_apply_apply] at t)
      (by have t := φ.symm.map_rel_iff.2 h2; rwa [RelIso.symm_apply_apply] at t)
      (φ.symm.map_rel_iff.2 h3)

theorem bibd_block_clique_graph_iso_local {X₁ B₁ X₂ B₂ : Type*} {v b r k lam : ℕ}
    (D₁ : BIBD X₁ B₁ v b r k lam) (D₂ : BIBD X₂ B₂ v b r k lam) (hk : 3 ≤ k)
    (φ : bibd_block_clique_graph D₁ ≃g bibd_block_clique_graph D₂) (β : B₁) (j : Fin k) :
    ∃ β' j', φ (Sum.inr (β, j)) = Sum.inr (β', j') := by
  rcases h : φ (Sum.inr (β, j)) with y | ⟨β', j'⟩
  · exfalso
    obtain ⟨a, c, h1, h2, h3⟩ := bibd_block_clique_graph_local_triangle D₁ hk β j
    exact bibd_block_clique_graph_point_no_triangle D₂ y (φ a) (φ c)
      (by rw [← h]; exact φ.map_rel_iff.2 h1)
      (by rw [← h]; exact φ.map_rel_iff.2 h2)
      (φ.map_rel_iff.2 h3)
  · exact ⟨β', j', rfl⟩

theorem bibd_isomorphic_of_block_clique_graph_iso_of_three_le {X₁ B₁ X₂ B₂ : Type*}
    {v b r k lam : ℕ} (D₁ : BIBD X₁ B₁ v b r k lam) (D₂ : BIBD X₂ B₂ v b r k lam) (hk : 3 ≤ k)
    (h : Nonempty (bibd_block_clique_graph D₁ ≃g bibd_block_clique_graph D₂)) :
    bibd_isomorphic D₁ D₂ := by
  obtain ⟨φ⟩ := h
  let j0 : Fin k := ⟨0, by omega⟩
  choose f hf using bibd_block_clique_graph_iso_point D₁ D₂ hk φ
  choose f' hf' using bibd_block_clique_graph_iso_point D₂ D₁ hk φ.symm
  choose g κ hg using bibd_block_clique_graph_iso_local D₁ D₂ hk φ
  choose g' κ' hg' using bibd_block_clique_graph_iso_local D₂ D₁ hk φ.symm
  have same : ∀ (β : B₁) (j : Fin k), g β j = g β j0 := by
    intro β j
    by_cases e : j = j0
    · rw [e]
    · have hadj : (bibd_block_clique_graph D₁).Adj (Sum.inr (β, j)) (Sum.inr (β, j0)) := by
        simpa [bibd_block_clique_graph] using e
      have := φ.map_rel_iff.2 hadj
      rw [hg, hg] at this
      simp only [bibd_block_clique_graph] at this
      exact this.1
  have same' : ∀ (β : B₂) (j : Fin k), g' β j = g' β j0 := by
    intro β j
    by_cases e : j = j0
    · rw [e]
    · have hadj : (bibd_block_clique_graph D₂).Adj (Sum.inr (β, j)) (Sum.inr (β, j0)) := by
        simpa [bibd_block_clique_graph] using e
      have := φ.symm.map_rel_iff.2 hadj
      rw [hg', hg'] at this
      simp only [bibd_block_clique_graph] at this
      exact this.1
  let F : X₁ ≃ X₂ :=
    { toFun := f, invFun := f'
      left_inv := by
        intro x
        have h1 : φ.symm (Sum.inl (f x)) = Sum.inl x := by rw [← hf]; simp
        rw [hf' (f x)] at h1
        exact Sum.inl.inj h1
      right_inv := by
        intro y
        have h1 : φ (Sum.inl (f' y)) = Sum.inl y := by rw [← hf']; simp
        rw [hf (f' y)] at h1
        exact Sum.inl.inj h1 }
  let G : B₁ ≃ B₂ :=
    { toFun := fun β => g β j0, invFun := fun β => g' β j0
      left_inv := by
        intro β
        have h1 : φ.symm (Sum.inr (g β j0, κ β j0)) = Sum.inr (β, j0) := by rw [← hg]; simp
        rw [hg'] at h1
        have h2 := (Prod.mk.inj (Sum.inr.inj h1)).1
        show g' (g β j0) j0 = β
        rw [same' _ (κ β j0)] at *
        exact h2
      right_inv := by
        intro β
        have h1 : φ (Sum.inr (g' β j0, κ' β j0)) = Sum.inr (β, j0) := by rw [← hg']; simp
        rw [hg] at h1
        have h2 := (Prod.mk.inj (Sum.inr.inj h1)).1
        show g (g' β j0) j0 = β
        rw [same _ (κ' β j0)] at *
        exact h2 }
  refine ⟨F, G, fun β x => ?_⟩
  show (∃ j, D₁.block_pts β j = x) ↔ ∃ j', D₂.block_pts (g β j0) j' = f x
  constructor
  · rintro ⟨j, rfl⟩
    have hadj : (bibd_block_clique_graph D₁).Adj (Sum.inr (β, j)) (Sum.inl (D₁.block_pts β j)) := by
      simp [bibd_block_clique_graph]
    have := φ.map_rel_iff.2 hadj
    rw [hg, hf] at this
    simp only [bibd_block_clique_graph] at this
    exact ⟨κ β j, by rw [← same β j]; exact this⟩
  · rintro ⟨j', hj'⟩
    have hadj : (bibd_block_clique_graph D₂).Adj (Sum.inr (g β j0, j')) (Sum.inl (f x)) := by
      simpa [bibd_block_clique_graph] using hj'
    have := φ.symm.map_rel_iff.2 hadj
    have e1 : φ.symm (Sum.inl (f x)) = Sum.inl x := by rw [← hf]; simp
    rw [e1, hg'] at this
    simp only [bibd_block_clique_graph] at this
    refine ⟨κ' (g β j0) j', ?_⟩
    have e2 : g' (g β j0) j' = β := by
      have h1 : φ.symm (Sum.inr (g β j0, κ β j0)) = Sum.inr (β, j0) := by rw [← hg]; simp
      rw [hg'] at h1
      rw [same' _ j', ← same' _ (κ β j0)]
      exact (Prod.mk.inj (Sum.inr.inj h1)).1
    rw [e2] at this
    exact this
