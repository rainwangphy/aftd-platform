import AFTD.Prelude
import AFTD.Kb.Tcs.IsMinimalTernaryLineCover
import AFTD.Kb.Tcs.TernaryAffineHyperplane
import AFTD.Kb.Tcs.TernarySinglePointRepair
import AFTD.Kb.Tcs.IsTernaryLineCover

/-!
# ternary_single_point_repair_is_minimal_line_cover

Topic: combinatorics   Node: 52bbff7538b8

Provenance: formalization of a published result. Source: arXiv:2610.32789, Section 3.1

For every explicit integer n ≥ 3, every vector a : Fin n → ZMod 3 with all coordinates nonzero, every scalar b : ZMod 3, every point p in ternary_affine_hyperplane n a b, and every vector ε : Fin n → ZMod 3 with all coordinates nonzero, the finite set ternary_single_point_repair n (ternary_affine_hyperplane n a b) p ε is an inclusion-minimal ternary line cover.
-/

/-- Every single-point repair of an affine hyperplane is an inclusion-minimal line cover for n ≥ 3. -/
theorem ternary_single_point_repair_is_minimal_line_cover (n : ℕ) (hn : 3 ≤ n) (a : Fin n → ZMod 3) (ha : ∀ i, a i ≠ 0) (b : ZMod 3) (p : Fin n → ZMod 3) (hp : p ∈ ternary_affine_hyperplane n a b) (ε : Fin n → ZMod 3) (hε : ∀ i, ε i ≠ 0) : is_minimal_ternary_line_cover n (ternary_single_point_repair n (ternary_affine_hyperplane n a b) p ε) := by
  set H := ternary_affine_hyperplane n a b with hH
  set B := ternary_single_point_repair n H p ε with hB
  have hp' : p ∈ H := by rw [hH]; exact hp
  have hsum : ∀ (c : Fin n → ZMod 3) (i : Fin n) (t : ZMod 3),
      ∑ j, a j * Function.update c i t j = (∑ j ∈ Finset.univ.erase i, a j * c j) + a i * t := by
    intro c i t
    rw [← Finset.sum_erase_add Finset.univ (fun j => a j * Function.update c i t j) (Finset.mem_univ i)]
    congr 1
    · exact Finset.sum_congr rfl fun j hj => by rw [Function.update_of_ne (Finset.ne_of_mem_erase hj)]
    · rw [Function.update_self]
  have hmemH : ∀ x : Fin n → ZMod 3, x ∈ H ↔ ∑ j, a j * x j = b := by
    intro x; rw [hH]; simp [ternary_affine_hyperplane]
  have hBunf : B = H.erase p ∪ Finset.image (fun j => Function.update p j (p j + ε j)) Finset.univ := by
    rw [hB, hH]; rfl
  have hmemB : ∀ x : Fin n → ZMod 3, x ∈ B ↔ (x ∈ H ∧ x ≠ p) ∨ ∃ j, Function.update p j (p j + ε j) = x := by
    intro x
    rw [hBunf, Finset.mem_union, Finset.mem_erase, Finset.mem_image]
    simp only [Finset.mem_univ, true_and]
    tauto
  have hagree : ∀ (i : Fin n) (x y : Fin n → ZMod 3), x ∈ H → y ∈ H →
      (∀ k, k ≠ i → x k = y k) → x = y := by
    intro i x y hx hy hag
    rw [hmemH] at hx hy
    have hx' := hsum x i (x i)
    simp only [Function.update_eq_self] at hx'
    have hy' := hsum y i (y i)
    simp only [Function.update_eq_self] at hy'
    have hS : ∑ j ∈ Finset.univ.erase i, a j * x j = ∑ j ∈ Finset.univ.erase i, a j * y j :=
      Finset.sum_congr rfl fun j hj => by rw [hag j (Finset.ne_of_mem_erase hj)]
    have heq : (∑ j ∈ Finset.univ.erase i, a j * x j) + a i * x i = (∑ j ∈ Finset.univ.erase i, a j * y j) + a i * y i := by
      rw [← hx', ← hy', hx, hy]
    rw [hS] at heq
    have h4 : x i = y i := mul_left_cancel₀ (ha i) (add_left_cancel heq)
    funext k
    by_cases hk : k = i
    · subst hk; exact h4
    · exact hag k hk
  have hP_notMem : ∀ j, Function.update p j (p j + ε j) ∉ H := by
    intro j hmem
    rw [hmemH] at hmem
    rw [hsum] at hmem
    have hpS : (∑ k ∈ Finset.univ.erase j, a k * p k) + a j * p j = b := by
      have h := hsum p j (p j)
      simp only [Function.update_eq_self] at h
      rw [← h]
      exact (hmemH p).mp hp'
    have h2 : a j * (p j + ε j) = a j * p j := add_left_cancel (hmem.trans hpS.symm)
    rw [mul_add] at h2
    have h3 : a j * ε j = 0 := by
      have h4 : a j * p j + a j * ε j = a j * p j + 0 := by rw [add_zero]; exact h2
      exact add_left_cancel h4
    rcases mul_eq_zero.mp h3 with h0 | h0
    · exact ha j h0
    · exact hε j h0
  have hP_ne_p : ∀ j, Function.update p j (p j + ε j) ≠ p := by
    intro j h
    exact hP_notMem j (h.symm ▸ hp')
  have hP_inj : ∀ j j', Function.update p j (p j + ε j) = Function.update p j' (p j' + ε j') → j = j' := by
    intro j j' h
    by_contra hne
    have h1 := congr_fun h j
    rw [Function.update_self, Function.update_of_ne hne] at h1
    have h2 : p j + ε j = p j + 0 := by rw [add_zero]; exact h1
    exact hε j (add_left_cancel h2)
  have hP_notOnPline : ∀ (i j : Fin n), j ≠ i → ∀ t : ZMod 3,
      Function.update p i t ≠ Function.update p j (p j + ε j) := by
    intro i j hji t h
    have h1 := congr_fun h j
    rw [Function.update_of_ne hji, Function.update_self] at h1
    have h2 : p j + ε j = p j + 0 := by rw [add_zero]; exact h1.symm
    exact hε j (add_left_cancel h2)
  have hkey : ∀ (x : Fin n → ZMod 3) (i : Fin n) (t : ZMod 3) (j : Fin n),
      x ∈ H → x ≠ p → Function.update x i t = Function.update p j (p j + ε j) →
      j ≠ i ∧ x i ≠ p i ∧ x j ≠ p j ∧ ∀ k, k ≠ i → k ≠ j → x k = p k := by
    intro x i t j hx hxp h
    have hoff : ∀ k, k ≠ i → k ≠ j → x k = p k := by
      intro k hki hkj
      have h1 := congr_fun h k
      rw [Function.update_of_ne hki, Function.update_of_ne hkj] at h1
      exact h1
    have hji : j ≠ i := by
      intro h_eq
      exact hxp (hagree i x p hx hp' (fun k hk => hoff k hk (h_eq.symm ▸ hk)))
    have hxi : x i ≠ p i := by
      intro h_eq
      refine hxp (hagree j x p hx hp' (fun k hk => ?_))
      by_cases hki : k = i
      · rw [hki]; exact h_eq
      · exact hoff k hki hk
    have hxj : x j ≠ p j := by
      have h1 := congr_fun h j
      rw [Function.update_of_ne hji, Function.update_self] at h1
      intro h_eq
      have h3 : p j = p j + ε j := h_eq.symm.trans h1
      have h4 : p j + 0 = p j + ε j := by rw [add_zero]; exact h3
      have h5 : (0 : ZMod 3) = ε j := add_left_cancel h4
      exact hε j h5.symm
    exact ⟨hji, hxi, hxj, hoff⟩
  have hexists_ne_two : ∀ i j : Fin n, ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
    intro i j
    by_contra h
    have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j} := by
      intro k _
      by_cases hki : k = i
      · simp [hki]
      · have hkj : k = j := by
          by_contra hkj
          exact h ⟨k, hki, hkj⟩
        simp [hkj]
    have hc := Finset.card_le_card hsub
    rw [Finset.card_univ, Fintype.card_fin] at hc
    have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := by
      by_cases hij : i = j
      · simp [hij]
      · simp [hij]
    omega
  have hcover : is_ternary_line_cover n B := by
    intro i c
    obtain ⟨t₀, ht₀⟩ : ∃ t, Function.update c i t ∈ H := by
      refine ⟨(a i)⁻¹ * (b - ∑ j ∈ Finset.univ.erase i, a j * c j), ?_⟩
      rw [hmemH, hsum, ← mul_assoc, mul_inv_cancel₀ (ha i), one_mul]
      ring
    by_cases hpc : Function.update c i t₀ = p
    · refine ⟨p i + ε i, ?_⟩
      have heq : Function.update c i (p i + ε i) = Function.update p i (p i + ε i) := by
        funext k
        by_cases hk : k = i
        · rw [hk, Function.update_self, Function.update_self]
        · rw [Function.update_of_ne hk, Function.update_of_ne hk]
          have := congr_fun hpc k
          rw [Function.update_of_ne hk] at this
          exact this
      rw [heq, hmemB]
      exact Or.inr ⟨i, rfl⟩
    · refine ⟨t₀, ?_⟩
      rw [hmemB]
      exact Or.inl ⟨ht₀, hpc⟩
  refine ⟨hcover, ?_⟩
  intro B' hB'sub hB'cover
  apply Finset.Subset.antisymm hB'sub
  intro x hx
  rw [hmemB] at hx
  rcases hx with ⟨hxH, hxp⟩ | ⟨j, rfl⟩
  · obtain ⟨i₀, hi₀⟩ : ∃ k, x k ≠ p k := by
      by_contra h
      exact hxp (funext fun k => by by_contra hk; exact h ⟨k, hk⟩)
    obtain ⟨t₁, ht₁⟩ := hB'cover i₀ x
    have h1B : Function.update x i₀ t₁ ∈ B := hB'sub ht₁
    rw [hmemB] at h1B
    rcases h1B with ⟨hH1, _⟩ | ⟨j₁, hj₁⟩
    · have heq : Function.update x i₀ t₁ = x :=
        hagree i₀ _ x hH1 hxH (fun k hk => by rw [Function.update_of_ne hk])
      rwa [heq] at ht₁
    · obtain ⟨hji, _, hxj, hoff⟩ := hkey x i₀ t₁ j₁ hxH hxp hj₁.symm
      obtain ⟨k, hk1, hk2⟩ := hexists_ne_two i₀ j₁
      obtain ⟨t₂, ht₂⟩ := hB'cover k x
      have h2B : Function.update x k t₂ ∈ B := hB'sub ht₂
      rw [hmemB] at h2B
      rcases h2B with ⟨hH2, _⟩ | ⟨j₂, hj₂⟩
      · have heq : Function.update x k t₂ = x :=
          hagree k _ x hH2 hxH (fun m hm => by rw [Function.update_of_ne hm])
        rwa [heq] at ht₂
      · obtain ⟨_, _, _, hoff₂⟩ := hkey x k t₂ j₂ hxH hxp hj₂.symm
        have e1 : j₂ = i₀ := by
          by_contra hne
          exact hi₀ (hoff₂ i₀ hk1.symm (Ne.symm hne))
        have e2 : j₂ = j₁ := by
          by_contra hne
          exact hxj (hoff₂ j₁ hk2.symm (Ne.symm hne))
        exact absurd (e2.symm.trans e1) hji
  · obtain ⟨t, ht⟩ := hB'cover j p
    have h1B : Function.update p j t ∈ B := hB'sub ht
    rw [hmemB] at h1B
    rcases h1B with ⟨hH, hne⟩ | ⟨j', hj'⟩
    · have heq : Function.update p j t = p :=
        hagree j _ p hH hp' (fun k hk => by rw [Function.update_of_ne hk])
      exact absurd heq hne
    · have hjj : j' = j := by
        by_contra hne
        exact hP_notOnPline j j' hne t hj'.symm
      rw [hjj] at hj'
      rw [hj']
      exact ht
