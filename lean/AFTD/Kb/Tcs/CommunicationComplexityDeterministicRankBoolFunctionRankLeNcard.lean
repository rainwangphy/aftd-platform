import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicRankBoolFunctionMatrix
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicRankBoolFunctionRank
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicRankRankRectMatrixLeOne
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicRankRectMatrix
import AFTD.Kb.Tcs.MatrixRankSumLe
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsMonoPartition
import AFTD.Kb.Tcs.CommunicationComplexityRectangleMonoPartitionPartUnique
import AFTD.Kb.Tcs.CommunicationComplexityRectangleMonoPartitionPointMem
import AFTD.Kb.Tcs.CommunicationComplexityRectangleMonoPartitionValuesEq

/-!
# CommunicationComplexity.Deterministic.Rank.boolFunctionRank_le_ncard

Topic: communication   Node: c73ef8e0148e

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Deterministic.Rank.boolFunctionRank_le_ncard`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/Rank.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Rank bounded by monochromatic partition size. Let $X$ be a finite set, $Y$ a finite set, and $f : X \to Y \to \mathrm{Bool}$ a Boolean
function. If $\mathcal{P}$ is a monochromatic rectangle partition of $X \times Y$ for
$f$, then the rank of $f$ is at most the number of members of $\mathcal{P}$:
\[
\mathrm{rank}(f) \le \abs{\mathcal{P}}.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open CommunicationComplexity.Rectangle in
/-- The rank of a Boolean function `f` is at most the number of rectangles in any monochromatic rectangle partition of its input space [RY20, Lemma 2.10]. Deviation: [RY20] states the bound `≤ 2 ^ c` for a partition into `2 ^ c` parts; here the bound is the number of parts itself, for an arbitrary finite partition. **Proof sketch.** Step 1: let `trueRects` be the parts of the partition that contain some input on which `f` is `true`; by monochromaticity `f` is `true` throughout each of them. Step 2: the communication matrix `M_f` equals the sum of the indicator matrices of the parts in `trueRects`. Entrywise, the input `(x, y)` lies in exactly one part `R₀`, so all other indicator matrices vanish at `(x, y)`: if `f x y = false` then `R₀` is not in `trueRects` and every term is `0`; if `f x y = true` then `R₀` is in `trueRects` and contributes `1`. Step 3: rank is subadditive over the sum (`Matrix.rank_sum_le`), each rectangle indicator matrix has rank at most `1` (`rank_rectMatrix_le_one`), and `trueRects` is a subset of the partition, so `rank(M_f) ≤ |trueRects| ≤ |Part|`. -/
theorem CommunicationComplexity.Deterministic.Rank.boolFunctionRank_le_ncard
    {X Y : Type*} [Finite X] [Fintype Y]
    (f : X → Y → Bool)
    (Part : Set (Set (X × Y)))
    (hPart : Rectangle.IsMonoPartition Part f) :
    boolFunctionRank f ≤ Set.ncard Part := by
  classical
  -- Step 1: the parts containing a `true` input
  let PF := (Set.toFinite Part).toFinset
  let trueRects := PF.filter (fun R => ∃ p ∈ R, f p.1 p.2 = true)
  -- Step 2: M_f = ∑ over true-mono rectangles of rectMatrix R
  have hsum : boolFunctionMatrix f = ∑ R ∈ trueRects, rectMatrix R := by
    ext x y
    simp only [boolFunctionMatrix, rectMatrix, Matrix.of_apply, Matrix.sum_apply]
    obtain ⟨R₀, hR₀_mem, hR₀_in⟩ := monoPartition_point_mem hPart (x, y)
    have hother : ∀ R ∈ PF, R ≠ R₀ → (x, y) ∉ R := fun R hR hne hmem =>
      hne (monoPartition_part_unique hPart
        ((Set.toFinite Part).mem_toFinset.mp hR) hR₀_mem hmem hR₀_in)
    cases hf : f x y <;> simp only [Bool.false_eq_true, ite_true, ite_false]
    · -- f x y = false: every term is 0
      symm; apply Finset.sum_eq_zero; intro R hR
      by_cases hne : R = R₀
      · subst hne; obtain ⟨⟨x', y'⟩, hpin, hftrue⟩ := (Finset.mem_filter.mp hR).2
        have hmono := monoPartition_values_eq hPart hR₀_mem hR₀_in hpin
        rw [hf] at hmono; simp [← hmono] at hftrue
      · simp [hother R (Finset.mem_filter.mp hR).1 hne]
    · -- f x y = true: only R₀ contributes 1
      symm; rw [Finset.sum_eq_single R₀
        (fun R hR hne => by simp [hother R (Finset.mem_filter.mp hR).1 hne])
        (fun h => absurd (Finset.mem_filter.mpr
          ⟨(Set.toFinite Part).mem_toFinset.mpr hR₀_mem, ⟨x, y⟩, hR₀_in, hf⟩) h)]
      simp [hR₀_in]
  -- Step 3: rank(M_f) ≤ ∑ rank(rectMatrix R) ≤ ∑ 1 = |trueRects| ≤ |Part|
  calc boolFunctionRank f
      = (∑ R ∈ trueRects, rectMatrix R).rank := by unfold boolFunctionRank; rw [← hsum]
    _ ≤ ∑ R ∈ trueRects, (rectMatrix R).rank := Matrix.rank_sum_le _ _
    _ ≤ ∑ _R ∈ trueRects, 1 := Finset.sum_le_sum fun R hR =>
        rank_rectMatrix_le_one R (hPart.1 R ((Set.toFinite Part).mem_toFinset.mp
          (Finset.mem_filter.mp hR).1))
    _ = trueRects.card := by simp
    _ ≤ PF.card := Finset.card_filter_le _ _
    _ = Set.ncard Part := (Set.ncard_eq_toFinset_card Part (Set.toFinite Part)).symm
