import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsMatroidRankValuation
import AFTD.Kb.GameTheoryEconomics.IsPmmsFair
import AFTD.Kb.GameTheoryEconomics.MaximinShare
import AFTD.Kb.GameTheoryEconomics.BundleOf
import AFTD.Kb.GameTheoryEconomics.HasBinaryMarginals
import AFTD.Kb.GameTheoryEconomics.IsSubmodular
import AFTD.Kb.GameTheoryEconomics.PairwiseMaximinShare
import AFTD.Kb.GameTheoryEconomics.SubmodUnionMarginalLe
import AFTD.Kb.GameTheoryEconomics.SubmodBiUnionLeSum

/-!
# complete_pmms_matroid_rank_sharp_mms_factor

Topic: fair_division   Node: 04dd0549ec0c

Provenance: formalization of a published result. Source: arXiv:2012.12710

For every integer n ≥ 2, every finite set of m indivisible goods, every profile of matroid-rank valuations v_1, ..., v_n on the goods, and every complete allocation σ that is pairwise maximin-share (PMMS) fair, every agent i receives at least a 1/(n-1) fraction of her maximin share: MMS_i(n, M) ≤ (n - 1) * v_i(bundle_of σ i).
-/

/-- OP-598: In complete PMMS allocations under matroid-rank valuations, is (n-1) v_i(A_i) ≥ MMS_i(n, M) for all agents? -/
theorem complete_pmms_matroid_rank_sharp_mms_factor :
    ∀ (n m : ℕ) (hn : 2 ≤ n) (v : Fin n → Finset (Fin m) → ℝ),
      (∀ i, is_matroid_rank_valuation (v i)) →
      ∀ σ : Fin m → Fin n, (∀ i, is_pmms_fair v σ i) →
        ∀ i : Fin n, maximin_share (v i) n ≤ (n - 1 : ℝ) * v i (bundle_of σ i) := by
  intro n m hn v hv σ hpmms i
  set r : Finset (Fin m) → ℝ := v i with hr
  obtain ⟨hzero, hsub, hbin⟩ := hv i
  have hz : r ∅ = 0 := hzero
  have hstep : ∀ (S : Finset (Fin m)) (x : Fin m), x ∉ S → r S ≤ r (insert x S) := by
    intro S x hx
    rcases hbin S x hx with h | h <;> linarith
  have hmono : Monotone r := by
    have key : ∀ (U S : Finset (Fin m)), r S ≤ r (S ∪ U) := by
      intro U
      induction U using Finset.induction_on with
      | empty => intro S; simp
      | insert x U hx ih =>
          intro S
          rw [Finset.union_insert]
          by_cases hxS : x ∈ S
          · rw [Finset.insert_eq_of_mem (by simp [hxS])]; exact ih S
          · exact le_trans (ih S) (hstep (S ∪ U) x (by simp [hxS, hx]))
    intro S T hST
    have h := key (T \ S) S
    rwa [Finset.union_sdiff_of_subset hST] at h
  have hnonneg : ∀ S : Finset (Fin m), 0 ≤ r S := by
    intro S
    have h := hmono (Finset.empty_subset S)
    rwa [hz] at h
  have hadd : ∀ S T : Finset (Fin m), r (S ∪ T) ≤ r S + r T := by
    intro S T
    have h := submod_union_marginal_le r hmono hsub (S := ∅) (T := S) (Finset.empty_subset S) T
    simp only [Finset.empty_union, hz] at h
    linarith
  set A : Finset (Fin m) := bundle_of σ i with hA
  set a : ℝ := r A with ha
  have hpair : ∀ j, j ≠ i → ∀ T : Finset (Fin m), T ⊆ A ∪ bundle_of σ j →
      min (r T) (r ((A ∪ bundle_of σ j) \ T)) ≤ a := by
    intro j hj T hT
    have hsup : pairwise_maximin_share r (A ∪ bundle_of σ j) ≤ a := by
      have h := hpmms i j hj
      rwa [hr, hA, ha]
    have hbdd : BddAbove (Set.range fun T : {T : Finset (Fin m) // T ⊆ A ∪ bundle_of σ j} =>
        min (r T.1) (r ((A ∪ bundle_of σ j) \ T.1))) := by
      refine ⟨r (A ∪ bundle_of σ j), ?_⟩
      rintro _ ⟨T, rfl⟩
      exact le_trans (min_le_left _ _) (hmono T.2)
    have hle : min (r T) (r ((A ∪ bundle_of σ j) \ T))
        ≤ pairwise_maximin_share r (A ∪ bundle_of σ j) := by
      rw [pairwise_maximin_share]
      exact le_ciSup hbdd ⟨T, hT⟩
    linarith
  rw [maximin_share]
  haveI : Nonempty (Fin m → Fin n) := ⟨fun _ => ⟨0, by omega⟩⟩
  apply ciSup_le
  intro P
  let bad : Fin n → Finset (Fin n) := fun j =>
    Finset.univ.filter (fun k : Fin n => a < r (bundle_of P k ∩ (A ∪ bundle_of σ j)))
  have hcard : ∀ j ∈ (Finset.univ.erase i), (bad j).card ≤ 1 := by
    intro j hj
    rw [Finset.card_le_one]
    intro k hk k' hk'
    by_contra hne
    have hk1 : a < r (bundle_of P k ∩ (A ∪ bundle_of σ j)) := (Finset.mem_filter.mp hk).2
    have hk2 : a < r (bundle_of P k' ∩ (A ∪ bundle_of σ j)) := (Finset.mem_filter.mp hk').2
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have hdisj : Disjoint (bundle_of P k) (bundle_of P k') := by
      rw [Finset.disjoint_left]
      intro x hx hx'
      simp only [bundle_of, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
      exact hne (hx.symm.trans hx')
    have hsub' : bundle_of P k' ∩ (A ∪ bundle_of σ j) ⊆
        (A ∪ bundle_of σ j) \ (bundle_of P k ∩ (A ∪ bundle_of σ j)) := by
      intro x hx
      simp only [Finset.mem_inter, Finset.mem_sdiff] at hx ⊢
      exact ⟨hx.2, fun h => Finset.disjoint_left.mp hdisj h.1 hx.1⟩
    have hT := hpair j hji (bundle_of P k ∩ (A ∪ bundle_of σ j)) Finset.inter_subset_right
    have hgt : a < r ((A ∪ bundle_of σ j) \ (bundle_of P k ∩ (A ∪ bundle_of σ j))) :=
      lt_of_lt_of_le hk2 (hmono hsub')
    have hlt : a < min (r (bundle_of P k ∩ (A ∪ bundle_of σ j)))
        (r ((A ∪ bundle_of σ j) \ (bundle_of P k ∩ (A ∪ bundle_of σ j)))) := lt_min hk1 hgt
    linarith
  have hScard : ((Finset.univ.erase i).biUnion bad).card ≤ n - 1 := by
    have h1 : ((Finset.univ.erase i).biUnion bad).card ≤ ∑ j ∈ (Finset.univ.erase i), (bad j).card :=
      Finset.card_biUnion_le
    have h2 : ∑ j ∈ (Finset.univ.erase i), (bad j).card ≤ ∑ j ∈ (Finset.univ.erase i), (1:ℕ) :=
      Finset.sum_le_sum hcard
    have h3 : ∑ j ∈ (Finset.univ.erase i), (1:ℕ) = n - 1 := by
      rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
        Fintype.card_fin]
      simp
    omega
  have hex : ∃ k : Fin n, k ∉ (Finset.univ.erase i).biUnion bad := by
    by_contra h
    simp only [not_exists, not_not] at h
    have hSfull : (Finset.univ.erase i).biUnion bad = Finset.univ := Finset.eq_univ_of_forall h
    have hc : ((Finset.univ.erase i).biUnion bad).card = n := by
      rw [hSfull, Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨kstar, hkstar⟩ := hex
  have hkstar_le : ∀ j, j ≠ i → r (bundle_of P kstar ∩ (A ∪ bundle_of σ j)) ≤ a := by
    intro j hj
    have hmem : j ∈ Finset.univ.erase i := Finset.mem_erase.mpr ⟨hj, Finset.mem_univ j⟩
    have hnot : kstar ∉ bad j := by
      intro hk
      exact hkstar (Finset.mem_biUnion.mpr ⟨j, hmem, hk⟩)
    have hnot' : ¬ (a < r (bundle_of P kstar ∩ (A ∪ bundle_of σ j))) := by
      intro hlt
      exact hnot (Finset.mem_filter.mpr ⟨Finset.mem_univ _, hlt⟩)
    exact not_lt.mp hnot'
  have hJpos : 0 < (Finset.univ.erase i : Finset (Fin n)).card := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  obtain ⟨j0, hj0mem⟩ := Finset.card_pos.mp hJpos
  have hj0ne : j0 ≠ i := (Finset.mem_erase.mp hj0mem).1
  have hcover : bundle_of P kstar ⊆
      (bundle_of P kstar ∩ (A ∪ bundle_of σ j0)) ∪
        (((Finset.univ.erase i).erase j0).biUnion (fun j => bundle_of P kstar ∩ bundle_of σ j)) := by
    intro x hx
    by_cases hxi : σ x = i
    · refine Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, ?_⟩)
      exact Finset.mem_union_left _ (by simp [A, bundle_of, hxi])
    · by_cases hxj : σ x = j0
      · refine Finset.mem_union_left _ (Finset.mem_inter.mpr ⟨hx, ?_⟩)
        exact Finset.mem_union_right _ (by simp [bundle_of, hxj])
      · refine Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨σ x, ?_, ?_⟩)
        · simp only [Finset.mem_erase, Finset.mem_univ, and_true]
          exact ⟨hxj, hxi⟩
        · exact Finset.mem_inter.mpr ⟨hx, by simp [bundle_of]⟩
  have h1 : r (bundle_of P kstar) ≤ r (bundle_of P kstar ∩ (A ∪ bundle_of σ j0)) +
      r (((Finset.univ.erase i).erase j0).biUnion (fun j => bundle_of P kstar ∩ bundle_of σ j)) :=
    le_trans (hmono hcover) (hadd _ _)
  have h2 : r (bundle_of P kstar ∩ (A ∪ bundle_of σ j0)) ≤ a := hkstar_le j0 hj0ne
  have h3 : r (((Finset.univ.erase i).erase j0).biUnion (fun j => bundle_of P kstar ∩ bundle_of σ j)) ≤
      ∑ j ∈ (Finset.univ.erase i).erase j0, r (bundle_of P kstar ∩ bundle_of σ j) :=
    submod_biUnion_le_sum r hmono hsub hz _ _
  have h4 : ∑ j ∈ (Finset.univ.erase i).erase j0, r (bundle_of P kstar ∩ bundle_of σ j) ≤
      ∑ j ∈ (Finset.univ.erase i).erase j0, a := by
    apply Finset.sum_le_sum
    intro j hj
    have hji : j ≠ i := (Finset.mem_erase.mp (Finset.mem_erase.mp hj).2).1
    have hBJ : bundle_of P kstar ∩ bundle_of σ j ⊆ bundle_of P kstar ∩ (A ∪ bundle_of σ j) := by
      intro x hx
      simp only [Finset.mem_inter] at hx ⊢
      exact ⟨hx.1, Finset.mem_union_right _ hx.2⟩
    exact le_trans (hmono hBJ) (hkstar_le j hji)
  have h5 : ∑ j ∈ (Finset.univ.erase i).erase j0, a = (((Finset.univ.erase i).erase j0 : Finset (Fin n)).card : ℝ) * a := by
    rw [Finset.sum_const, nsmul_eq_mul]
  have h6 : ((Finset.univ.erase i).erase j0 : Finset (Fin n)).card = n - 2 := by
    rw [Finset.card_erase_of_mem (Finset.mem_erase.mpr ⟨hj0ne, Finset.mem_univ j0⟩)]
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
    omega
  have h7 : ((n - 2 : ℕ) : ℝ) = (n : ℝ) - 2 := Nat.cast_sub (by omega : 2 ≤ n)
  have hbound : r (bundle_of P kstar) ≤ (n - 1 : ℝ) * a := by
    have h6' : ((((Finset.univ.erase i).erase j0 : Finset (Fin n)).card : ℕ) : ℝ) = ((n - 2 : ℕ) : ℝ) := by rw [h6]
    rw [h6', h7] at h5
    nlinarith [h1, h2, h3, h4, h5]
  have hbdd : BddBelow (Set.range fun k : Fin n => r (bundle_of P k)) :=
    ⟨0, by rintro _ ⟨k, rfl⟩; exact hnonneg _⟩
  exact le_trans (ciInf_le hbdd kstar) hbound
