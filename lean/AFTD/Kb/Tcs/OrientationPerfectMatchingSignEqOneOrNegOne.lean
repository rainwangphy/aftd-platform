import AFTD.Prelude
import AFTD.Kb.Tcs.OrientationPerfectMatchingSign
import AFTD.Kb.Tcs.IsGraphOrientation

/-!
# orientation_perfect_matching_sign_eq_one_or_neg_one

Topic: combinatorics   Node: 2ca5a72ee44b

Provenance: helper lemma. arXiv:2611.00468 (The symbolic pfaffian method I), Section 1.1 (the sign of a perfect matching is ±1)

If D is an orientation of a simple graph G on Fin n (is_graph_orientation G D) and M is a perfect matching of G, then orientation_perfect_matching_sign D M is 1 or -1.
-/

theorem orientation_perfect_matching_sign_eq_one_or_neg_one {n : ℕ} (G : SimpleGraph (Fin n))
    (D : Digraph (Fin n)) (hD : is_graph_orientation G D) (M : G.Subgraph)
    (hM : M.IsPerfectMatching) :
    orientation_perfect_matching_sign D M = 1 ∨ orientation_perfect_matching_sign D M = -1 := by
  classical
  -- the partner map
  have hex : ∀ v, ∃! w, M.Adj v w := fun v => hM.1 (hM.2 v)
  choose p hp huniq using hex
  have hpp : ∀ v, p (p v) = v := fun v => (huniq (p v) v (hp v).symm).symm
  have hpinj : Function.Injective p := fun a b h => by rw [← hpp a, h, hpp b]
  set T : Finset (Fin n) := Finset.univ.filter (fun v => D.Adj v (p v)) with hT
  have hxor : ∀ v, v ∈ T ↔ p v ∉ T := by
    intro v
    have hG : G.Adj v (p v) := M.adj_sub (hp v)
    have h1 := (hD.1 v (p v)).mpr hG
    have h2 := hD.2 v (p v)
    simp only [hT, Finset.mem_filter, Finset.mem_univ, true_and, hpp]
    tauto
  have hcard : 2 * T.card = n := by
    have hdisj : Disjoint T (T.image p) := by
      rw [Finset.disjoint_left]
      intro a ha hb
      obtain ⟨b, hbT, rfl⟩ := Finset.mem_image.mp hb
      exact ((hxor b).mp hbT) ha
    have hunion : T ∪ T.image p = Finset.univ := by
      ext v
      simp only [Finset.mem_union, Finset.mem_image, Finset.mem_univ, iff_true]
      by_cases hv : v ∈ T
      · exact Or.inl hv
      · right; exact ⟨p v, (hxor (p v)).mpr (by rw [hpp]; exact hv), hpp v⟩
    have := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin, Finset.card_image_of_injective _ hpinj] at this
    omega
  set m := T.card with hm
  let e : Fin m → Fin n := fun i => (T.equivFin.symm i : Fin n)
  have he_mem : ∀ i, e i ∈ T := fun i => (T.equivFin.symm i).2
  have he_inj : Function.Injective e := fun a b h =>
    T.equivFin.symm.injective (Subtype.ext h)
  let f : Fin n → Fin n := fun i =>
    if i.val % 2 = 0 then e ⟨i.val / 2, by omega⟩ else p (e ⟨i.val / 2, by omega⟩)
  have hf_inj : Function.Injective f := by
    intro a b hab
    simp only [f] at hab
    split_ifs at hab with ha hb hb
    · have := congrArg Fin.val (he_inj hab); simp at this; ext; omega
    · exact absurd (hab ▸ he_mem _) ((hxor _).mp (he_mem _))
    · exact absurd (hab.symm ▸ he_mem _) ((hxor _).mp (he_mem _))
    · have := congrArg Fin.val (he_inj (hpinj hab)); simp at this; ext; omega
  let π : Equiv.Perm (Fin n) := Equiv.ofBijective f (Finite.injective_iff_bijective.mp hf_inj)
  have hπ : ∃ π : Equiv.Perm (Fin n), ∀ (j : ℕ) (hj : 2 * j + 1 < n),
      M.Adj (π ⟨2 * j, by omega⟩) (π ⟨2 * j + 1, hj⟩) ∧
        D.Adj (π ⟨2 * j, by omega⟩) (π ⟨2 * j + 1, hj⟩) := by
    refine ⟨π, fun j hj => ?_⟩
    have h0 : π ⟨2 * j, by omega⟩ = e ⟨j, by omega⟩ := by
      show f ⟨2 * j, by omega⟩ = _
      simp only [f]
      rw [if_pos (by simp)]
      congr 1; ext; simp
    have h1 : π ⟨2 * j + 1, hj⟩ = p (e ⟨j, by omega⟩) := by
      show f ⟨2 * j + 1, hj⟩ = _
      simp only [f]
      rw [if_neg (by omega)]
      congr 2; ext; simp only; omega
    rw [h0, h1]
    refine ⟨hp _, ?_⟩
    have := he_mem ⟨j, by omega⟩
    simpa [hT] using this
  unfold orientation_perfect_matching_sign
  rw [dif_pos hπ]
  rcases Int.units_eq_one_or (Equiv.Perm.sign hπ.choose) with h | h <;> rw [h] <;> simp
