import AFTD.Prelude
import AFTD.Kb.Optimization.MatroidBaseBall
import AFTD.Kb.Optimization.MatroidDiam
import AFTD.Kb.Optimization.ExistsBaseBallImage

/-!
# metric_ball_volume_comparison_matroid_bases

Topic: submodular   Node: 9e97595dc21e

Provenance: formalization of a published result. Source: arXiv:2611.27934 Lemma 4.11 -- The Power of Sampling for Finding Far-Apart Bases in Matroids

For every finite matroid M on a type α, any two bases A, B of M (satisfying M.IsBase A and M.IsBase B), and every natural number r, the cardinality (ncard) of the basis ball matroid_base_ball M A r is at most 4^(matroid_diam M) times the cardinality (ncard) of matroid_base_ball M B (2 * r).
-/

open Set in
private lemma metric_ball_volume_comparison_matroid_bases_aux {α : Type*} (M : Matroid α) [M.Finite]
    {A Y : Set α} (hA : M.IsBase A) (hY : M.IsBase Y) :
    ({X : Set α | X \ A ⊆ Y \ A ∧ A \ X ⊆ A \ Y}).ncard ≤ 4 ^ (matroid_diam M) := by
  classical
  set S : Set (Set α) := {X : Set α | X \ A ⊆ Y \ A ∧ A \ X ⊆ A \ Y} with hS
  have key : ∀ X : Set α, X = (A \ (A \ X)) ∪ (X \ A) := by
    intro X; ext x
    simp only [Set.mem_union, Set.mem_sdiff]
    tauto
  have hinj : Set.InjOn (fun X : Set α => (A \ X, X \ A)) S := by
    intro X1 _ X2 _ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    rw [key X1, key X2, h1, h2]
  have hsub : (fun X : Set α => (A \ X, X \ A)) '' S ⊆ (𝒫 (A \ Y)) ×ˢ (𝒫 (Y \ A)) := by
    rintro p ⟨X, hX, rfl⟩
    exact ⟨hX.2, hX.1⟩
  have hfinA : (A \ Y).Finite := hA.finite.subset sdiff_subset
  have hfinYA : (Y \ A).Finite := hY.finite.subset sdiff_subset
  have hfinprod : ((𝒫 (A \ Y)) ×ˢ (𝒫 (Y \ A))).Finite := hfinA.powerset.prod hfinYA.powerset
  have h1 : S.ncard ≤ ((𝒫 (A \ Y)) ×ˢ (𝒫 (Y \ A))).ncard :=
    Set.ncard_le_ncard_of_injOn _ (fun X hX => hsub ⟨X, hX, rfl⟩) hinj hfinprod
  rw [Set.ncard_prod, Set.ncard_powerset (A \ Y) hfinA, Set.ncard_powerset (Y \ A) hfinYA] at h1
  have heq : (Y \ A).ncard = (A \ Y).ncard := (hA.ncard_sdiff_comm hY).symm
  have hbdd : BddAbove { (A' \ B').ncard | (A' : Set α) (B' : Set α) (_ : M.IsBase A') (_ : M.IsBase B') } := by
    refine ⟨M.E.ncard, ?_⟩
    rintro b ⟨A', B', hA', hB', rfl⟩
    exact Set.ncard_le_ncard ((Set.sdiff_subset).trans hA'.subset_ground) M.ground_finite
  have hmem : (A \ Y).ncard ∈ { (A' \ B').ncard | (A' : Set α) (B' : Set α) (_ : M.IsBase A') (_ : M.IsBase B') } :=
    ⟨A, Y, hA, hY, rfl⟩
  have hdle : (A \ Y).ncard ≤ matroid_diam M := by
    rw [matroid_diam]
    exact le_csSup hbdd hmem
  refine h1.trans ?_
  rw [heq]
  calc 2 ^ (A \ Y).ncard * 2 ^ (A \ Y).ncard = (2 * 2) ^ (A \ Y).ncard := (Nat.mul_pow 2 2 _).symm
    _ = 4 ^ (A \ Y).ncard := by norm_num
    _ ≤ 4 ^ matroid_diam M := Nat.pow_le_pow_right (by norm_num) hdle

/-- Metric ball volume comparison for matroid bases: |Ball_M(A, r)| ≤ 4^{diam(M)} |Ball_M(B, 2r)|. -/
theorem metric_ball_volume_comparison_matroid_bases {α : Type*} (M : Matroid α) [M.Finite]
    (A B : Set α) (hA : M.IsBase A) (hB : M.IsBase B) (r : ℕ) :
    (matroid_base_ball M A r).ncard ≤ 4 ^ (matroid_diam M) * (matroid_base_ball M B (2 * r)).ncard := by
  classical
  set T : Set α → Set (Set α) := fun Y => {X : Set α | X \ A ⊆ Y \ A ∧ A \ X ⊆ A \ Y} with hT
  have hsub : matroid_base_ball M A r ⊆ ⋃ Y ∈ matroid_base_ball M B (2*r), T Y := by
    intro X hX
    obtain ⟨Y, hY, h1, h2⟩ := exists_base_ball_image M hA hB r hX
    exact Set.mem_biUnion hY (show X ∈ T Y from ⟨h1, h2⟩)
  have hfinB : (matroid_base_ball M B (2*r)).Finite :=
    M.ground_finite.powerset.subset (fun X hX => hX.1.subset_ground)
  have hunion_sub : (⋃ Y ∈ matroid_base_ball M B (2*r), T Y) ⊆ 𝒫 M.E := by
    intro X hX
    rw [Set.mem_iUnion] at hX
    obtain ⟨Y, hY⟩ := hX
    rw [Set.mem_iUnion] at hY
    obtain ⟨hYmem, hXY⟩ := hY
    show X ∈ 𝒫 M.E
    have hYbase : M.IsBase Y := hYmem.1
    intro x hx
    by_cases hxA : x ∈ A
    · exact hA.subset_ground hxA
    · exact hYbase.subset_ground (hXY.1 ⟨hx, hxA⟩).1
  have hfinU : (⋃ Y ∈ matroid_base_ball M B (2*r), T Y).Finite :=
    M.ground_finite.powerset.subset hunion_sub
  have step1 : (matroid_base_ball M A r).ncard ≤ (⋃ Y ∈ matroid_base_ball M B (2*r), T Y).ncard :=
    Set.ncard_le_ncard hsub hfinU
  have step2 : (⋃ Y ∈ matroid_base_ball M B (2*r), T Y).ncard
      ≤ ∑ Y ∈ hfinB.toFinset, (T Y).ncard := by
    have h := Finset.set_ncard_biUnion_le hfinB.toFinset T
    simpa [Set.Finite.mem_toFinset] using h
  have step3 : ∑ Y ∈ hfinB.toFinset, (T Y).ncard ≤ ∑ Y ∈ hfinB.toFinset, 4 ^ (matroid_diam M) := by
    apply Finset.sum_le_sum
    intro Y hY
    exact metric_ball_volume_comparison_matroid_bases_aux M hA (hfinB.mem_toFinset.mp hY).1
  have step4 : ∑ Y ∈ hfinB.toFinset, 4 ^ (matroid_diam M) = hfinB.toFinset.card * 4 ^ (matroid_diam M) :=
    Finset.sum_const_nat (fun _ _ => rfl)
  calc (matroid_base_ball M A r).ncard
      ≤ (⋃ Y ∈ matroid_base_ball M B (2*r), T Y).ncard := step1
    _ ≤ ∑ Y ∈ hfinB.toFinset, (T Y).ncard := step2
    _ ≤ ∑ Y ∈ hfinB.toFinset, 4 ^ (matroid_diam M) := step3
    _ = hfinB.toFinset.card * 4 ^ (matroid_diam M) := step4
    _ = 4 ^ (matroid_diam M) * (matroid_base_ball M B (2*r)).ncard := by
        rw [Set.ncard_eq_toFinset_card _ hfinB, Nat.mul_comm]
