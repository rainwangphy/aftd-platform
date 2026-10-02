import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsSubmodular
import AFTD.Kb.GameTheoryEconomics.IsMxsFair
import AFTD.Kb.GameTheoryEconomics.IsProp1Fair
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.SubmodUnionMarginalLe
import AFTD.Kb.GameTheoryEconomics.SubmodBiUnionLeSum
import AFTD.Kb.GameTheoryEconomics.SubmodAddItemsLe
import AFTD.Kb.GameTheoryEconomics.SubmodZeroMarginals

/-!
# mxs_fair_imp_prop1_fair_of_submodular

Topic: fair_division   Node: deca533ea1c3

Garg-Sharma open problem 3 has a positive answer: for submodular goods (monotone, v(empty) = 0) and equal entitlements, every MXS-fair allocation is PROP1-fair. Proof: take an EFX certificate X, B_1..B_{n-1} with v(X) <= v(A); if A is not PROP1, put delta = v(M)/n - v(A) > 0, and pick from each B_j an item g_j outside A with positive marginal over X when there is one (k such items, G). Then v(B_j - g_j) <= v(X), and v(M) <= v(M - G) + k delta. If k = n - 1, v(M - G) <= n v(X); otherwise the remaining items outside A have zero marginal over X and v(M - G) <= (k + 2) v(A). Either way v(M) < n (v(A) + delta) = v(M).
-/

/-- Garg-Sharma open problem 3 (arXiv:2502.02815 v3, Sec. 6) has a positive answer: for submodular goods and equal entitlements, every MXS-fair allocation is PROP1-fair. -/
theorem mxs_fair_imp_prop1_fair_of_submodular :
    ∀ (n m : ℕ) (v : Fin n → Finset (Fin m) → ℝ),
      (∀ i, v i ∅ = 0 ∧ Monotone (v i) ∧ is_submodular (v i)) →
      ∀ (σ : Fin m → Fin n) (i : Fin n), is_mxs_fair v σ i →
        is_prop1_fair (v i) (1 / n) (bundle_of σ i) := by
  classical
  intro n m v hv σ i hmxs
  obtain ⟨τ, hefx, hle⟩ := hmxs
  obtain ⟨h0, hmono, hsub⟩ := hv i
  have hn : (0 : ℝ) < n := by exact_mod_cast Nat.lt_of_le_of_lt (Nat.zero_le _) i.2
  set u := v i with hu
  set A := bundle_of σ i with hA
  set X := bundle_of τ i with hX
  set V := u Finset.univ with hV
  -- suppose not PROP1
  by_contra hcon
  simp only [is_prop1_fair, not_or, not_exists, not_and, not_lt, not_le] at hcon
  obtain ⟨hAlt, hadd, -⟩ := hcon
  set δ := 1 / (n : ℝ) * V - u A with hδdef
  have hδ : 0 < δ := by rw [hδdef]; linarith
  have hVn : V = n * (u A + δ) := by rw [hδdef]; field_simp; ring
  have huA0 : 0 ≤ u A := by rw [← h0]; exact hmono (Finset.empty_subset _)
  -- no items: then A is everything
  rcases isEmpty_or_nonempty (Fin m) with hm | hm
  · have e1 : A = ∅ := Subsingleton.elim _ _
    have e2 : (Finset.univ : Finset (Fin m)) = ∅ := Subsingleton.elim _ _
    rw [e1, e2, h0] at hAlt
    simp at hAlt
  -- the bundles of the EFX certificate τ
  have hmemB : ∀ x, x ∈ bundle_of τ (τ x) := fun x => by simp [bundle_of]
  let P : Fin n → Fin m → Prop := fun j x => x ∈ bundle_of τ j ∧ x ∉ A ∧ u X < u (insert x X)
  let K : Finset (Fin n) := (Finset.univ.erase i).filter (fun j => ∃ x, P j x)
  let g : Fin n → Fin m := fun j => Classical.epsilon (P j)
  have hg : ∀ j ∈ K, P j (g j) := fun j hj =>
    Classical.epsilon_spec (Finset.mem_filter.1 hj).2
  have hKi : ∀ j ∈ K, j ≠ i := fun j hj => (Finset.mem_erase.1 (Finset.mem_filter.1 hj).1).1
  -- EFX with S = {g j}
  have hefxK : ∀ j ∈ K, u ((bundle_of τ j).erase (g j)) ≤ u X := by
    intro j hj
    obtain ⟨hgB, -, hgpos⟩ := hg j hj
    rcases hefx j (hKi j hj) with h | ⟨h1, -⟩
    · exact le_trans (hmono (Finset.erase_subset _ _)) h
    · have := h1 {g j} (Finset.singleton_subset_iff.2 hgB)
        (by rw [Finset.union_singleton]; exact hgpos)
      rwa [Finset.sdiff_singleton_eq_erase] at this
  let G := K.image g
  let W := X ∪ K.biUnion (fun j => (bundle_of τ j).erase (g j))
  have hW : u W ≤ u X + K.card * u X := by
    have h1 := submod_union_marginal_le u hmono hsub (Finset.empty_subset X)
      (K.biUnion (fun j => (bundle_of τ j).erase (g j)))
    rw [Finset.empty_union, h0] at h1
    have h2 := submod_biUnion_le_sum u hmono hsub h0 K (fun j => (bundle_of τ j).erase (g j))
    have h3 : ∑ j ∈ K, u ((bundle_of τ j).erase (g j)) ≤ K.card * u X := by
      have := Finset.sum_le_sum hefxK
      simpa using this
    linarith
  have hGadd : ∀ x ∈ G, x ∉ A ∧ u (insert x A) ≤ u A + δ := by
    intro x hx
    obtain ⟨j, hj, rfl⟩ := Finset.mem_image.1 hx
    have hgA := (hg j hj).2.1
    exact ⟨hgA, by have := hadd (g j) hgA; linarith⟩
  have hGcard : (G.card : ℝ) ≤ K.card := by exact_mod_cast Finset.card_image_le
  have hXW : X ⊆ W := Finset.subset_union_left
  have huXA : u X ≤ u A := hle
  have hKsub : K ⊆ Finset.univ.erase i := Finset.filter_subset _ _
  have hcardE : (Finset.univ.erase i).card + 1 = n := by
    rw [Finset.card_erase_add_one (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  by_cases hK : K = Finset.univ.erase i
  · -- every bundle other than i's has a positive item outside A
    have hcov : ∀ x, x ∉ G → x ∈ W := by
      intro x hxG
      by_cases hx : τ x = i
      · exact Finset.mem_union_left _ (by simp [hX, bundle_of, hx])
      · have hj : τ x ∈ K := by rw [hK]; exact Finset.mem_erase.2 ⟨hx, Finset.mem_univ _⟩
        have hxg : x ≠ g (τ x) := fun h => hxG (Finset.mem_image.2 ⟨τ x, hj, h.symm⟩)
        exact Finset.mem_union_right _
          (Finset.mem_biUnion.2 ⟨τ x, hj, Finset.mem_erase.2 ⟨hxg, hmemB x⟩⟩)
    have hAW : A ⊆ W := fun x hxA => hcov x (fun hxG => (hGadd x hxG).1 hxA)
    have hun : Finset.univ ⊆ W ∪ G := fun x _ => by
      by_cases hxG : x ∈ G
      · exact Finset.mem_union_right _ hxG
      · exact Finset.mem_union_left _ (hcov x hxG)
    have h1 : V ≤ u (W ∪ G) := hmono hun
    have h2 := submod_add_items_le u hsub hAW hδ.le G hGadd
    have hKc : (K.card : ℝ) + 1 = n := by rw [hK]; exact_mod_cast hcardE
    have h3 : (K.card : ℝ) * u X ≤ K.card * u A :=
      mul_le_mul_of_nonneg_left huXA (Nat.cast_nonneg _)
    have h4 : (G.card : ℝ) * δ ≤ K.card * δ := mul_le_mul_of_nonneg_right hGcard hδ.le
    -- V ≤ n u(A) + (n-1) δ < n (u(A) + δ) = V
    have : V ≤ (K.card + 1) * u A + K.card * δ := by nlinarith
    rw [hKc] at this
    nlinarith
  · -- some other bundle has no positive item outside A
    have hss : K ⊂ Finset.univ.erase i := Finset.ssubset_iff_subset_ne.2 ⟨hKsub, hK⟩
    have hKlt : K.card < (Finset.univ.erase i).card := Finset.card_lt_card hss
    have hKc : (K.card : ℝ) + 2 ≤ n := by
      have : K.card + 2 ≤ n := by omega
      exact_mod_cast this
    let R := Finset.univ.filter (fun x => x ∉ A ∧ τ x ≠ i ∧ τ x ∉ K)
    have hR : ∀ z ∈ R, u (insert z X) ≤ u X := by
      intro z hz
      obtain ⟨hzA, hzi, hzK⟩ := (Finset.mem_filter.1 hz).2
      by_contra hlt
      rw [not_le] at hlt
      exact hzK (Finset.mem_filter.2
        ⟨Finset.mem_erase.2 ⟨hzi, Finset.mem_univ _⟩, ⟨z, hmemB z, hzA, hlt⟩⟩)
    let W' := W ∪ A
    have hun : Finset.univ ⊆ (W' ∪ R) ∪ G := by
      intro x _
      by_cases hx : τ x = i
      · exact Finset.mem_union_left _ (Finset.mem_union_left _
          (Finset.mem_union_left _ (Finset.mem_union_left _ (by simp [hX, bundle_of, hx]))))
      by_cases hxA : x ∈ A
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_right _ hxA))
      by_cases hj : τ x ∈ K
      · by_cases hxg : x = g (τ x)
        · exact Finset.mem_union_right _ (Finset.mem_image.2 ⟨τ x, hj, hxg.symm⟩)
        · exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_union_left _
            (Finset.mem_union_right _
              (Finset.mem_biUnion.2 ⟨τ x, hj, Finset.mem_erase.2 ⟨hxg, hmemB x⟩⟩))))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _
          (Finset.mem_filter.2 ⟨Finset.mem_univ _, hxA, hx, hj⟩))
    have hAW' : A ⊆ W' ∪ R := fun x hx => Finset.mem_union_left _ (Finset.mem_union_right _ hx)
    have h1 : V ≤ u ((W' ∪ R) ∪ G) := hmono hun
    have h2 := submod_add_items_le u hsub hAW' hδ.le G hGadd
    have h3 : u (W' ∪ R) = u W' :=
      submod_zero_marginals u hmono hsub (hXW.trans Finset.subset_union_left) R hR
    have h4 : u W' ≤ u W + u A := by
      have := submod_union_marginal_le u hmono hsub (Finset.empty_subset W) A
      rw [Finset.empty_union, h0] at this
      linarith
    have h5 : (K.card : ℝ) * u X ≤ K.card * u A :=
      mul_le_mul_of_nonneg_left huXA (Nat.cast_nonneg _)
    have h6 : (G.card : ℝ) * δ ≤ K.card * δ := mul_le_mul_of_nonneg_right hGcard hδ.le
    have h7 : ((K.card : ℝ) + 2) * u A ≤ n * u A := mul_le_mul_of_nonneg_right hKc huA0
    have h8 : (K.card : ℝ) * δ ≤ (n - 2) * δ := mul_le_mul_of_nonneg_right (by linarith) hδ.le
    nlinarith
