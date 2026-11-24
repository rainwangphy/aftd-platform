import AFTD.Prelude
import AFTD.Kb.Optimization.MatroidBaseBall
import AFTD.Kb.Tcs.Order
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# exists_base_ball_image

Topic: submodular   Node: 1073c5b57d17

Provenance: helper lemma. arXiv:2611.27934, Lemma 4.11

Let M be a finite matroid, and let A, B be bases of M. For every base X in Ball_M(A, r), there exists a base Y in Ball_M(B, 2r) such that X \ A ⊆ Y \ A and A \ X ⊆ A \ Y.
-/

lemma exists_base_ball_image_phase1_lemma {α : Type*} (M : Matroid α) [M.Finite]
    {X S : Set α} (hX : M.IsBase X)
    (hS : S ⊆ M.E) (hdj : Disjoint S X) :
    ∀ (n : ℕ) (B : Set α), M.IsBase B → (B ∩ S).ncard = n →
      ∃ B', M.IsBase B' ∧ Disjoint S B' ∧ (B \ B').ncard ≤ (B ∩ S).ncard ∧ B \ B' ⊆ S := by
  intro n
  induction' n with n ih
  · intro B hB hn
    have hfin : (B ∩ S).Finite := M.ground_finite.subset (Set.inter_subset_right.trans hS)
    rw [Set.ncard_eq_zero hfin] at hn
    refine ⟨B, hB, ?_, by simp, by simp⟩
    rw [Set.disjoint_iff_inter_eq_empty, Set.inter_comm, hn]
  · intro B hB hn
    have hfin : (B ∩ S).Finite := M.ground_finite.subset (Set.inter_subset_right.trans hS)
    have hne : (B ∩ S).Nonempty := by
      rw [Set.nonempty_iff_ne_empty]
      intro h
      simp [h] at hn
    obtain ⟨e, ⟨heB, heS⟩⟩ := hne
    have heX : e ∉ X := fun heX ↦ hdj.le_bot ⟨heS, heX⟩
    have heBX : e ∈ B \ X := ⟨heB, heX⟩
    obtain ⟨y, hyX, hB₁⟩ := hB.exchange hX heBX
    have hyS : y ∉ S := fun hyS ↦ hdj.le_bot ⟨hyS, hyX.1⟩
    have hBS_eq : (insert y (B \ {e})) ∩ S = (B ∩ S) \ {e} := by
      ext x
      simp only [Set.mem_inter_iff, Set.mem_insert_iff, Set.mem_sdiff, Set.mem_singleton_iff]
      constructor
      · rintro ⟨rfl | ⟨hxB, hxe⟩, hxS⟩
        · exact (hyS hxS).elim
        · exact ⟨⟨hxB, hxS⟩, hxe⟩
      · rintro ⟨⟨hxB, hxS⟩, hxe⟩
        exact ⟨Or.inr ⟨hxB, hxe⟩, hxS⟩
    have hncard : ((insert y (B \ {e})) ∩ S).ncard = n := by
      rw [hBS_eq, Set.ncard_sdiff_singleton_of_mem (Set.mem_inter heB heS), hn, Nat.succ_sub_one]
    obtain ⟨B', hB'base, hB'dj, hdist, hsub⟩ := ih (insert y (B \ {e})) hB₁ hncard
    refine ⟨B', hB'base, hB'dj, ?_, ?_⟩
    · have hinc : B \ B' ⊆ insert e (insert y (B \ {e}) \ B') := by
        intro x hx
        by_cases hxe : x = e
        · rw [hxe]; exact Set.mem_insert e _
        · refine Set.mem_insert_of_mem _ ⟨Or.inr ⟨hx.1, hxe⟩, hx.2⟩
      have hfin_diff : (insert y (B \ {e}) \ B').Finite :=
        M.ground_finite.subset (Set.sdiff_subset.trans (Set.insert_subset (hX.subset_ground hyX.1)
          (Set.sdiff_subset.trans hB.subset_ground)))
      have hcard_le := (Set.ncard_le_ncard hinc (hfin_diff.insert e)).trans (Set.ncard_insert_le _ _)
      rw [hn]
      linarith
    · intro x hx
      by_cases hxe : x = e
      · rw [hxe]; exact heS
      · have : x ∈ insert y (B \ {e}) \ B' := ⟨Or.inr ⟨hx.1, hxe⟩, hx.2⟩
        exact hsub this

lemma exists_base_ball_image_phase1 {α : Type*} (M : Matroid α) [M.Finite]
    {B X S : Set α} (hB : M.IsBase B) (hX : M.IsBase X)
    (hS : S ⊆ M.E) (hdj : Disjoint S X) :
    ∃ B', M.IsBase B' ∧ Disjoint S B' ∧ (B \ B').ncard ≤ (B ∩ S).ncard ∧ B \ B' ⊆ S :=
  exists_base_ball_image_phase1_lemma M hX hS hdj (B ∩ S).ncard B hB rfl

/-- For any X in Ball(A, r), strong basis exchange yields Y in Ball(B, 2r) with X \ A ⊆ Y \ A and A \ X ⊆ A \ Y. -/
theorem exists_base_ball_image {α : Type*} (M : Matroid α) [M.Finite]
    {A B X : Set α} (hA : M.IsBase A) (hB : M.IsBase B) (r : ℕ)
    (hX : X ∈ matroid_base_ball M A r) :
    ∃ Y ∈ matroid_base_ball M B (2 * r), X \ A ⊆ Y \ A ∧ A \ X ⊆ A \ Y := by
  simp only [matroid_base_ball, Set.mem_ofPred_eq] at hX ⊢
  obtain ⟨hX_base, hX_card⟩ := hX
  set O := A \ X with hO_def
  have hO_sub : O ⊆ M.E := Set.sdiff_subset.trans hA.subset_ground
  have hO_dj : Disjoint O X := Set.disjoint_sdiff_left
  obtain ⟨B', hB'_base, hB'_dj, hB'_dist, hB'_sub⟩ :=
    exists_base_ball_image_phase1 M hB hX_base hO_sub hO_dj
  have hdual_fin : M✶.Finite := inferInstance
  set B'dual := M.E \ B' with hB'dual_def
  set Xdual := M.E \ X with hXdual_def
  have hB'dual_base : M✶.IsBase B'dual := hB'_base.compl_isBase_dual
  have hXdual_base : M✶.IsBase Xdual := hX_base.compl_isBase_dual
  set I := X \ A with hI_def
  have hI_sub : I ⊆ M✶.E := by
    rw [Matroid.dual_ground]
    exact Set.sdiff_subset.trans hX_base.subset_ground
  have hI_dj : Disjoint I Xdual := by
    rw [Set.disjoint_iff_inter_eq_empty]
    ext x
    simp only [Set.mem_inter_iff, Set.mem_empty_iff_false, iff_false]
    rintro ⟨⟨hxX, _⟩, ⟨-, hxX'⟩⟩
    exact hxX' hxX
  obtain ⟨Ydual, hYdual_base, hYdual_dj, hYdual_dist, hYdual_sub⟩ :=
    exists_base_ball_image_phase1 M✶ hB'dual_base hXdual_base hI_sub hI_dj
  set Y := M.E \ Ydual with hY_def
  have hY_base : M.IsBase Y := by
    rw [hY_def]
    exact hYdual_base.compl_isBase_of_dual
  refine ⟨Y, ⟨hY_base, ?_⟩, ?_, ?_⟩
  · have hBY_sub : B \ Y ⊆ (B \ B') ∪ (B' \ Y) := by
      intro x hx
      by_cases hxB' : x ∈ B'
      · exact Or.inr ⟨hxB', hx.2⟩
      · exact Or.inl ⟨hx.1, hxB'⟩
    have hB_B'_card : (B \ B').ncard ≤ r := by
      have hsub : B ∩ O ⊆ O := Set.inter_subset_right
      have hfin : O.Finite := M.ground_finite.subset hO_sub
      exact hB'_dist.trans ((Set.ncard_le_ncard hsub hfin).trans hX_card)
    have hB'_Y_eq : B' \ Y = Ydual \ B'dual := by
      ext x
      simp only [hY_def, hB'dual_def, Set.mem_sdiff]
      constructor
      · rintro ⟨hxB', hxY⟩
        have hxE := hB'_base.subset_ground hxB'
        have hxYd : x ∈ Ydual := by
          by_contra hc
          exact hxY ⟨hxE, hc⟩
        exact ⟨hxYd, fun ⟨_, h⟩ => h hxB'⟩
      · rintro ⟨hxYd, hxB'd⟩
        have hxE := hYdual_base.subset_ground hxYd
        have hxB' : x ∈ B' := by
          by_contra hc
          exact hxB'd ⟨hxE, hc⟩
        refine ⟨hxB', ?_⟩
        rintro ⟨-, hc⟩
        exact hc hxYd
    have hB'_Y_card : (B' \ Y).ncard ≤ r := by
      rw [hB'_Y_eq, hYdual_base.ncard_sdiff_comm hB'dual_base]
      have hsub : B'dual ∩ I ⊆ I := Set.inter_subset_right
      have hfin : I.Finite := M.ground_finite.subset (Set.sdiff_subset.trans hX_base.subset_ground)
      have hI_card : I.ncard ≤ r := by
        rw [hI_def, ← hA.ncard_sdiff_comm hX_base]
        exact hX_card
      exact hYdual_dist.trans ((Set.ncard_le_ncard hsub hfin).trans hI_card)
    have hfin_union : (B \ B' ∪ (B' \ Y)).Finite :=
      M.ground_finite.subset (Set.union_subset (Set.sdiff_subset.trans hB.subset_ground)
        (Set.sdiff_subset.trans hB'_base.subset_ground))
    have hle := (Set.ncard_le_ncard hBY_sub hfin_union).trans (Set.ncard_union_le (B \ B') (B' \ Y))
    linarith
  · intro x hx
    refine ⟨?_, hx.2⟩
    rw [hY_def, Set.mem_sdiff]
    refine ⟨hX_base.subset_ground hx.1, ?_⟩
    intro hxYd
    exact hYdual_dj.le_bot ⟨hx, hxYd⟩
  · intro x hx
    refine ⟨hx.1, ?_⟩
    rw [hY_def, Set.mem_sdiff, not_and]
    intro _ hxYd
    have hxB' : x ∉ B' := fun h ↦ hB'_dj.le_bot ⟨hx, h⟩
    have hxB'd : x ∈ B'dual := ⟨hA.subset_ground hx.1, hxB'⟩
    have hx_sdiff : x ∈ B'dual \ Ydual := ⟨hxB'd, hxYd⟩
    have hxI : x ∈ I := hYdual_sub hx_sdiff
    exact hxI.2 hx.1
