import AFTD.Prelude

/-!
# finset_family_card_sq_le_of_inter_symm_diff

Topic: combinatorics   Node: b15e4e7fc356

Provenance: helper lemma. Step toward zero_sum_w_two_le. arXiv:2610.19965 (Proofs and disproofs of some conjectures on zero-sum problems of new types), Theorem 1.2(i) w_r(2) = 2r + 1; the paper's upper bound classifies the w-bad sequences mod 4 (Theorem 3.1); this route replaces the classification by a counting argument.

A family K of subsets of a finite set U that contains the empty set, is closed under intersection and symmetric difference, and contains no singleton has |K|^2 <= 2^|U|.
-/

lemma finset_family_card_sq_le_of_inter_symm_diff_aux {ι : Type*} [DecidableEq ι] (n : ℕ) :
    ∀ (U : Finset ι) (K : Finset (Finset ι)), U.card = n →
    (∀ A ∈ K, A ⊆ U) → ∅ ∈ K →
    (∀ A ∈ K, ∀ B ∈ K, A ∩ B ∈ K) → (∀ A ∈ K, ∀ B ∈ K, symmDiff A B ∈ K) →
    (∀ x, ({x} : Finset ι) ∉ K) → K.card ^ 2 ≤ 2 ^ U.card := by
  classical
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro U K hU hsub h0 hinter hsd hsing
    rcases Finset.eq_empty_or_nonempty U with hUe | hUne
    · subst hUe
      have hKsub : K ⊆ {∅} := by
        intro A hA
        rw [Finset.mem_singleton]
        exact Finset.subset_empty.mp (hsub A hA)
      have hKeq : K = {∅} := Finset.Subset.antisymm hKsub (Finset.singleton_subset_iff.mpr h0)
      rw [hKeq]
      simp
    · obtain ⟨x, hxU⟩ := hUne
      by_cases hex : ∃ M ∈ K, x ∈ M
      · obtain ⟨M0, hM0K, hxM0⟩ := hex
        have hSne : (K.filter (fun M => x ∈ M)).Nonempty :=
          ⟨M0, Finset.mem_filter.mpr ⟨hM0K, hxM0⟩⟩
        obtain ⟨A, hAS, hAmin⟩ := Finset.exists_min_image (K.filter (fun M => x ∈ M)) Finset.card hSne
        have hAK : A ∈ K := (Finset.mem_filter.mp hAS).1
        have hxA : x ∈ A := (Finset.mem_filter.mp hAS).2
        have hAmin' : ∀ B ∈ K, x ∈ B → A.card ≤ B.card := by
          intro B hBK hxB
          exact hAmin B (Finset.mem_filter.mpr ⟨hBK, hxB⟩)
        have hkey : ∀ M ∈ K, Disjoint A M ∨ A ⊆ M := by
          intro M hMK
          by_cases hxM : x ∈ M
          · right
            have hAMK : A ∩ M ∈ K := hinter A hAK M hMK
            have hxAM : x ∈ A ∩ M := Finset.mem_inter.mpr ⟨hxA, hxM⟩
            have h1 : A.card ≤ (A ∩ M).card := hAmin' (A ∩ M) hAMK hxAM
            have h2 : A ∩ M ⊆ A := Finset.inter_subset_left
            have heq : A ∩ M = A := Finset.eq_of_subset_of_card_le h2 h1
            exact Finset.inter_eq_left.mp heq
          · left
            have hAMK : A ∩ M ∈ K := hinter A hAK M hMK
            have hxAM : x ∉ A ∩ M := by
              intro h; exact hxM (Finset.mem_inter.mp h).2
            have hsd' : symmDiff A (A ∩ M) ∈ K := hsd A hAK (A ∩ M) hAMK
            have hx' : x ∈ symmDiff A (A ∩ M) := by
              rw [Finset.mem_symmDiff]; exact Or.inl ⟨hxA, hxAM⟩
            have h1 : A.card ≤ (symmDiff A (A ∩ M)).card := hAmin' _ hsd' hx'
            have h2 : symmDiff A (A ∩ M) ⊆ A := by
              rw [symmDiff_of_ge (Finset.inter_subset_left : A ∩ M ⊆ A)]
              exact Finset.sdiff_subset
            have heq : symmDiff A (A ∩ M) = A := Finset.eq_of_subset_of_card_le h2 h1
            have heq' : A \ (A ∩ M) = A := by
              rw [← symmDiff_of_ge (Finset.inter_subset_left : A ∩ M ⊆ A)]
              exact heq
            have hdisj : Disjoint A (A ∩ M) := by
              rw [Finset.disjoint_left]
              intro y hyA hyAM
              have hy : y ∈ A \ (A ∩ M) := by rw [heq']; exact hyA
              exact (Finset.mem_sdiff.mp hy).2 hyAM
            have hAM : A ∩ M = ∅ := by
              have h := Finset.disjoint_iff_inter_eq_empty.mp hdisj
              rw [← Finset.inter_assoc, Finset.inter_self] at h
              exact h
            have hdisjAM : Disjoint A M := by
              rw [Finset.disjoint_left]
              intro y hyA hyM
              have hy : y ∈ A ∩ M := Finset.mem_inter.mpr ⟨hyA, hyM⟩
              rw [hAM] at hy
              simp at hy
            exact hdisjAM
        set K1 : Finset (Finset ι) := K.filter (fun M => Disjoint A M) with hK1def
        set K1c : Finset (Finset ι) := K.filter (fun M => ¬ Disjoint A M) with hK1cdef
        have hmem1 : ∀ M, M ∈ K1 ↔ M ∈ K ∧ Disjoint A M := by
          intro M; rw [hK1def]; exact Finset.mem_filter
        have hmem1c : ∀ M, M ∈ K1c ↔ M ∈ K ∧ ¬ Disjoint A M := by
          intro M; rw [hK1cdef]; exact Finset.mem_filter
        have hcard : K.card = K1.card + K1c.card := by
          have h := Finset.card_filter_add_card_filter_not (s := K) (p := fun M => Disjoint A M)
          rw [← hK1def, ← hK1cdef] at h
          exact h.symm
        have hf1 : ∀ M ∈ K1, symmDiff M A ∈ K1c := by
          intro M hM
          obtain ⟨hMK, hDM⟩ := (hmem1 M).mp hM
          have hK : symmDiff M A ∈ K := hsd M hMK A hAK
          have hnd : ¬ Disjoint A (symmDiff M A) := by
            intro hd
            have hxM : x ∉ M := (Finset.disjoint_left.mp hDM) hxA
            have hxmem : x ∈ symmDiff M A := by
              rw [Finset.mem_symmDiff]
              exact Or.inr ⟨hxA, hxM⟩
            exact ((Finset.disjoint_left.mp hd) hxA) hxmem
          exact (hmem1c _).mpr ⟨hK, hnd⟩
        have hf2 : ∀ M ∈ K1c, symmDiff M A ∈ K1 := by
          intro M hM
          obtain ⟨hMK, hndM⟩ := (hmem1c M).mp hM
          have hAM : A ⊆ M := (hkey M hMK).resolve_left hndM
          have hK : symmDiff M A ∈ K := hsd M hMK A hAK
          have hdisj : Disjoint A (symmDiff M A) := by
            have h1 : symmDiff M A = M \ A := symmDiff_of_ge hAM
            rw [h1, Finset.disjoint_left]
            intro y hyA hy
            exact (Finset.mem_sdiff.mp hy).2 hyA
          exact (hmem1 _).mpr ⟨hK, hdisj⟩
        have hff : ∀ M : Finset ι, symmDiff (symmDiff M A) A = M :=
          fun M => symmDiff_symmDiff_cancel_right A M
        have hinj : Function.Injective (fun M : Finset ι => symmDiff M A) := by
          intro M N h
          have h1 : symmDiff (symmDiff M A) A = symmDiff (symmDiff N A) A :=
            congrArg (fun L => symmDiff L A) h
          simpa only [hff] using h1
        have himage : K1.image (fun M => symmDiff M A) = K1c := by
          apply Finset.Subset.antisymm
          · intro M hM
            obtain ⟨N, hN, rfl⟩ := Finset.mem_image.mp hM
            exact hf1 N hN
          · intro M hM
            exact Finset.mem_image.mpr ⟨symmDiff M A, hf2 M hM, hff M⟩
        have hK1c_card : K1c.card = K1.card := by
          rw [← himage, Finset.card_image_of_injective _ hinj]
        have hKcard : K.card = 2 * K1.card := by
          rw [hcard, hK1c_card]
          ring
        have hAU : A ⊆ U := hsub A hAK
        have hAcard : 2 ≤ A.card := by
          by_contra h
          have hpos : 0 < A.card := Finset.card_pos.mpr ⟨x, hxA⟩
          have h1 : A.card = 1 := by omega
          obtain ⟨y, hy⟩ := Finset.card_eq_one.mp h1
          have hxy : x = y := by
            have hx : x ∈ ({y} : Finset ι) := by rw [← hy]; exact hxA
            simpa using hx
          rw [hy, ← hxy] at hAK
          exact hsing x hAK
        have hlt : (U \ A).card < n := by
          rw [← hU]
          have h1 : (U \ A).card = U.card - A.card := Finset.card_sdiff_of_subset hAU
          have h2 : A.card ≤ U.card := Finset.card_le_card hAU
          omega
        have hsub1 : ∀ M ∈ K1, M ⊆ U \ A := by
          intro M hM
          obtain ⟨hMK, hDM⟩ := (hmem1 M).mp hM
          rw [Finset.subset_sdiff]
          exact ⟨hsub M hMK, hDM.symm⟩
        have h01 : ∅ ∈ K1 := (hmem1 ∅).mpr ⟨h0, by simp⟩
        have hinter1 : ∀ M ∈ K1, ∀ N ∈ K1, M ∩ N ∈ K1 := by
          intro M hM N hN
          obtain ⟨hMK, hDM⟩ := (hmem1 M).mp hM
          obtain ⟨hNK, hDN⟩ := (hmem1 N).mp hN
          exact (hmem1 _).mpr ⟨hinter M hMK N hNK, Disjoint.mono le_rfl Finset.inter_subset_left hDM⟩
        have hsd1 : ∀ M ∈ K1, ∀ N ∈ K1, symmDiff M N ∈ K1 := by
          intro M hM N hN
          obtain ⟨hMK, hDM⟩ := (hmem1 M).mp hM
          obtain ⟨hNK, hDN⟩ := (hmem1 N).mp hN
          refine (hmem1 _).mpr ⟨hsd M hMK N hNK, ?_⟩
          rw [Finset.disjoint_left]
          intro y hyA hyMN
          rw [Finset.mem_symmDiff] at hyMN
          rcases hyMN with ⟨hyM, -⟩ | ⟨hyN, -⟩
          · exact ((Finset.disjoint_left.mp hDM) hyA) hyM
          · exact ((Finset.disjoint_left.mp hDN) hyA) hyN
        have hsing1 : ∀ y, ({y} : Finset ι) ∉ K1 := by
          intro y hy
          exact hsing y ((hmem1 _).mp hy).1
        have hIH := ih (U \ A).card hlt (U \ A) K1 rfl hsub1 h01 hinter1 hsd1 hsing1
        have hdlle : (U \ A).card + 2 ≤ U.card := by
          have h1 : (U \ A).card = U.card - A.card := Finset.card_sdiff_of_subset hAU
          have h2 : A.card ≤ U.card := Finset.card_le_card hAU
          omega
        have hpow : (4:ℕ) * 2 ^ (U \ A).card = 2 ^ ((U \ A).card + 2) := by
          rw [show (4:ℕ) = 2^2 by norm_num, ← pow_add, Nat.add_comm]
        calc K.card ^ 2 = (2 * K1.card) ^ 2 := by rw [hKcard]
          _ = 4 * K1.card ^ 2 := by ring
          _ ≤ 4 * 2 ^ (U \ A).card := Nat.mul_le_mul_left 4 hIH
          _ = 2 ^ ((U \ A).card + 2) := hpow
          _ ≤ 2 ^ U.card := Nat.pow_le_pow_right (by norm_num) hdlle
      · push Not at hex
        have hsub' : ∀ A ∈ K, A ⊆ U.erase x := by
          intro A hA
          rw [Finset.subset_erase]
          exact ⟨hsub A hA, hex A hA⟩
        have hlt : (U.erase x).card < n := by
          rw [← hU]
          exact Finset.card_erase_lt_of_mem hxU
        have hIH := ih (U.erase x).card hlt (U.erase x) K rfl hsub' h0 hinter hsd hsing
        calc K.card ^ 2 ≤ 2 ^ (U.erase x).card := hIH
          _ ≤ 2 ^ U.card := Nat.pow_le_pow_right (by norm_num) Finset.card_erase_le

theorem finset_family_card_sq_le_of_inter_symm_diff {ι : Type*} [DecidableEq ι] (U : Finset ι)
    (K : Finset (Finset ι)) (hsub : ∀ A ∈ K, A ⊆ U) (h0 : ∅ ∈ K)
    (hinter : ∀ A ∈ K, ∀ B ∈ K, A ∩ B ∈ K) (hsd : ∀ A ∈ K, ∀ B ∈ K, symmDiff A B ∈ K)
    (hsing : ∀ x, ({x} : Finset ι) ∉ K) :
    K.card ^ 2 ≤ 2 ^ U.card := finset_family_card_sq_le_of_inter_symm_diff_aux U.card U K rfl hsub h0 hinter hsd hsing
