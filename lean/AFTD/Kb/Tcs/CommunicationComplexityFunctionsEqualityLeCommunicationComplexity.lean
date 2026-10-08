import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicLeCommunicationComplexityOfForallLtNcard
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsEqualityEquality
import AFTD.Kb.Tcs.CommunicationComplexityBoolInput
import AFTD.Kb.Tcs.CommunicationComplexityRectangleMonoPartitionCrossMem
import AFTD.Kb.Tcs.CommunicationComplexityRectangleMonoPartitionPointMem
import AFTD.Kb.Tcs.CommunicationComplexityRectangleMonoPartitionValuesEq
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicProtocol
import AFTD.Kb.Tcs.CommunicationComplexityFlipAtApplySame
import AFTD.Kb.Tcs.CommunicationComplexityFlipAtApplyNe
import AFTD.Kb.Tcs.CommunicationComplexityFlipAtFlipAt

/-!
# CommunicationComplexity.Functions.Equality.le_communicationComplexity

Topic: communication   Node: 4f0fcde3536a

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Functions.Equality.le_communicationComplexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncEquality.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 adapted; compiled here.

Deterministic complexity lower bound for equality. For every natural number $n \ge 1$, the deterministic communication complexity of the
$n$-bit equality function satisfies
\[
  n + 1 \;\le\; D(\mathrm{equality}_n),
\]
where $\mathrm{equality}_n$ is the Boolean function on $\mathrm{BoolInput}\,n \times
\mathrm{BoolInput}\,n$ that returns $\mathtt{true}$ exactly when Alice's input equals
Bob's input.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open MeasureTheory in
open CommunicationComplexity.Deterministic.Protocol CommunicationComplexity.Rectangle in
/-- For `n ≥ 1`, the deterministic communication complexity of equality on `n`-bit strings is at least `n + 1` [RY20, Thm 1.14], via [RY20, Claim 1.13]: any monochromatic rectangle containing a diagonal point `(x, x)` contains no other diagonal point, so every monochromatic partition has at least `2 ^ n + 1` parts, which requires `n + 1` bits. **Proof sketch.** By the rectangle lower bound (`Deterministic.le_communicationComplexity_of_forall_lt_ncard`) it suffices to show that every monochromatic rectangle partition of the input space has more than `2 ^ n` parts. Step 1: for each string `x` choose a part `rect x` containing the diagonal point `(x, x)`. Step 2: `rect` is injective. If `rect x = rect y` with `x ≠ y`, then `(x, y)` lies in the same rectangle by the cross-membership property of rectangles, and monochromaticity forces `EQ(x, y) = EQ(x, x) = true`, contradicting `x ≠ y` (this is [RY20, Claim 1.13]). Step 3: hence the range of `rect` has exactly `2 ^ n` elements. Step 4: the part `R0` containing the off-diagonal point `(1ⁿ, 0ⁿ)` (which exists since `n ≥ 1`) is `false`-monochromatic, so it is not in the range of `rect`. Step 5: adjoining `R0` to the range of `rect` gives a subset of the partition with `2 ^ n + 1` parts. -/
theorem CommunicationComplexity.Functions.Equality.le_communicationComplexity (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℕ) ≤ Deterministic.communicationComplexity (equality n) := by
  apply Deterministic.le_communicationComplexity_of_forall_lt_ncard
  intro Part hPart
  -- Step 1: each (x,x) is in some rectangle in Part
  choose rect hrect_mem hrect_in using fun x =>
    monoPartition_point_mem hPart (x, x)
  -- Step 2: rect is injective: if rect x = rect y, then (x,x) and (y,y)
  -- are in the same rectangle, so (x,y) is too (cross_mem),
  -- and mono gives equality x x = equality x y, forcing x = y.
  have hrect_inj : Function.Injective rect := by
    intro x y hxy
    by_contra hne
    have hxy_mem := (monoPartition_cross_mem hPart (hrect_mem x)
      (hrect_in x) (hxy ▸ hrect_in y)).2
    have := monoPartition_values_eq hPart (hrect_mem x) (hrect_in x) hxy_mem
    simp [equality, hne] at this
  -- Step 3: the image of rect has size 2^n
  have himage_card :
      Set.ncard (Set.range rect) = 2 ^ n := by
    simpa [Fintype.card_bool, Fintype.card_fin] using
      Set.ncard_range_of_injective hrect_inj
  -- Step 4: find a "false" rectangle containing (x0, y0) with x0 ≠ y0
  have hx : (fun _ : Fin n => true) ≠ (fun _ : Fin n => false) := by
    intro h; have := congr_fun h ⟨0, hn⟩; simp at this
  set x0 : BoolInput n := fun _ => true
  set y0 : BoolInput n := fun _ => false
  obtain ⟨R0, hR0_mem, hR0_in⟩ := monoPartition_point_mem hPart (x0, y0)
  -- R0 is not in the image of rect: any rect z is "true"-mono,
  -- but R0 contains (x0, y0) with equality x0 y0 = false.
  have hR0_not_diag : R0 ∉ Set.range rect := by
    rintro ⟨z, rfl⟩
    have := monoPartition_values_eq hPart (hrect_mem z) (hrect_in z) hR0_in
    simp [equality, hx] at this
  -- Step 5: insert R0 into range rect ⊆ Part, giving 2^n < |Part|
  have hinsert : insert R0 (Set.range rect) ⊆ Part :=
    Set.insert_subset hR0_mem (fun R ⟨x, hx⟩ => hx ▸ hrect_mem x)
  calc 2 ^ n
      = Set.ncard (Set.range rect) := himage_card.symm
    _ < Set.ncard (insert R0 (Set.range rect)) := by
        rw [Set.ncard_insert_of_notMem hR0_not_diag, himage_card]; omega
    _ ≤ Set.ncard Part :=
        Set.ncard_le_ncard hinsert (Set.toFinite Part)
