import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicCommunicationComplexity
import AFTD.Kb.Tcs.CommunicationComplexityDeterministicLeCommunicationComplexityOfForallLtNcard
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsDisjointnessDisjointness
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsDisjointnessFoolingSet
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsDisjointnessFoolingSetIsFoolingSet
import AFTD.Kb.Tcs.CommunicationComplexityRectangleMonoPartitionPointMem
import AFTD.Kb.Tcs.CommunicationComplexityRectangleMonoPartitionValuesEq

/-!
# CommunicationComplexity.Functions.Disjointness.le_communicationComplexity

Topic: communication   Node: e94a1ffc6b68

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Functions.Disjointness.le_communicationComplexity`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncDisjointness.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Lower bound on the communication complexity of disjointness. Fix an integer $n \ge 1$, and consider the set-disjointness function on subsets of
$[n]$: it takes a pair of subsets $X, Y \subseteq [n]$ — Alice holding $X$ and Bob
holding $Y$ — to $\mathtt{true}$ exactly when $X \cap Y = \emptyset$. Then the
deterministic communication complexity of this function is at least $n + 1$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open CommunicationComplexity.Rectangle in
open scoped symmDiff in
/-- For `n ≥ 1`, disjointness on subsets of `[n]` has deterministic communication complexity at least `n + 1` [RY20, Thm 1.25]. Deviation: the bound is exact together with `communicationComplexity_le`; [Rou16, Cor 4.8] only gives `≥ n`. The hypothesis `n ≥ 1` is needed for an intersecting pair to exist. **Proof sketch.** By the rectangle lower bound (`Deterministic.le_communicationComplexity_of_forall_lt_ncard`) it suffices to show that every monochromatic rectangle partition of the input space has more than `2 ^ n` parts. Step 1: for each subset `X` choose a part `rect X` containing the fooling-set pair `(X, Xᶜ)`. Step 2: `rect` is injective, because a part containing both `(X, Xᶜ)` and `(X', X'ᶜ)` is a monochromatic rectangle, so the fooling-set property (`foolingSet_isFoolingSet`) forces `X = X'`. Step 3: hence the range of `rect` has exactly `2 ^ n` elements. Step 4: the part `R0` containing the intersecting pair `({0}, {0})` (which exists since `n ≥ 1`) is `false`-monochromatic, whereas every `rect X` contains the disjoint pair `(X, Xᶜ)` and is `true`-monochromatic; so `R0` is not in the range of `rect`. Step 5: adjoining `R0` to the range of `rect` gives a subset of the partition with `2 ^ n + 1` parts. -/
theorem CommunicationComplexity.Functions.Disjointness.le_communicationComplexity (n : ℕ) (hn : 1 ≤ n) :
    (n + 1 : ℕ) ≤ Deterministic.communicationComplexity (disjointness n) := by
  apply Deterministic.le_communicationComplexity_of_forall_lt_ncard
  intro Part hPart
  -- Step 1: each pair (X, Xᶜ) is in some rectangle in Part
  choose rect hrect_mem hrect_in using fun X : Set (Fin n) =>
    monoPartition_point_mem hPart (X, Xᶜ)
  -- Step 2: rect is injective by the fooling-set property
  have hrect_inj : Function.Injective rect := by
    intro X X' hXX
    have hsub :=
      foolingSet_isFoolingSet n (rect X) (hPart.1 _ (hrect_mem X)) (hPart.2.1 _ (hrect_mem X))
    have hp : (X, Xᶜ) ∈ foolingSet n ∩ rect X := by
      simp [foolingSet, hrect_in X]
    have hq : (X', X'ᶜ) ∈ foolingSet n ∩ rect X := by
      simp [foolingSet, hXX ▸ hrect_in X']
    exact congrArg Prod.fst (hsub hp hq)
  -- Step 3: the image of rect has size 2^n
  have himage_card :
      Set.ncard (Set.range rect) = 2 ^ n := by
    simpa [Fintype.card_set, Fintype.card_fin] using
      Set.ncard_range_of_injective hrect_inj
  -- Step 4: the rectangle R0 containing the intersecting pair ({0}, {0}) is "false"-mono,
  -- so it is not in the image of rect
  let i0 : Fin n := ⟨0, hn⟩
  let x0 : Set (Fin n) := {i0}
  let y0 : Set (Fin n) := {i0}
  obtain ⟨R0, hR0_mem, hR0_in⟩ := monoPartition_point_mem hPart (x0, y0)
  have hR0_not_diag : R0 ∉ Set.range rect := by
    rintro ⟨X, rfl⟩
    have hval := monoPartition_values_eq hPart (hrect_mem X) (hrect_in X) hR0_in
    have htrue : disjointness n X Xᶜ = true := by
      simpa [disjointness] using (disjoint_compl_right : Disjoint X Xᶜ)
    have hne : disjointness n x0 y0 ≠ true := by
      unfold disjointness
      simp only [ne_eq, decide_eq_true_eq]
      intro hdisj
      rw [Set.disjoint_left] at hdisj
      have hnot : i0 ∉ y0 := hdisj (by simp [x0])
      exact hnot (by simp [y0])
    rw [htrue] at hval
    exact (hne hval.symm).elim
  -- Step 5: insert R0 into range rect ⊆ Part, giving 2^n < |Part|
  have hinsert : insert R0 (Set.range rect) ⊆ Part :=
    Set.insert_subset hR0_mem (fun R ⟨X, hX⟩ => hX ▸ hrect_mem X)
  calc 2 ^ n
      = Set.ncard (Set.range rect) := himage_card.symm
    _ < Set.ncard (insert R0 (Set.range rect)) := by
        rw [Set.ncard_insert_of_notMem hR0_not_diag, himage_card]
        omega
    _ ≤ Set.ncard Part :=
        Set.ncard_le_ncard hinsert (Set.toFinite Part)
