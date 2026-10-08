import AFTD.Prelude
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsDisjointnessDisjointness
import AFTD.Kb.Tcs.CommunicationComplexityFunctionsDisjointnessFoolingSet
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsFoolingSet
import AFTD.Kb.Tcs.CommunicationComplexityRectangleIsRectangleIff

/-!
# CommunicationComplexity.Functions.Disjointness.foolingSet_isFoolingSet

Topic: communication   Node: 28724f58360b

Provenance: helper lemma. TCSlib, `CommunicationComplexity.Functions.Disjointness.foolingSet_isFoolingSet`. Lean proof by Lucy Horowitz, Timothe Kasriel, Mihir Singhal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/CommunicationComplexity/DeterministicCC/FuncDisjointness.lean (Copyright (c) 2026 Lucy Horowitz, Timothe Kasriel, and Mihir Singhal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The disjointness fooling set. Fix $n \in \bbn$, and consider the set-disjointness function on subsets of $[n]$, namely
the Boolean function $g(X, Y)$ that is $\mathtt{true}$ exactly when $X \cap Y =
\emptyset$. Then the collection $\{(X, X^c) \mid X \subseteq [n]\}$ of complementary
pairs is a fooling set for $g$: for every rectangle $R = A \times B$ (with $A, B$
families of subsets of $[n]$) that is monochromatic for $g$, the intersection of $R$
with this collection contains at most one point.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
open CommunicationComplexity.Rectangle in
open scoped symmDiff in
/-- The pairs `(X, Xᶜ)` form a fooling set for disjointness: no monochromatic rectangle contains two distinct pairs `(X, Xᶜ)` and `(X', X'ᶜ)` [RY20, Ch. 1, §Using Fooling Sets]. **Proof sketch.** Let `R` be a monochromatic rectangle containing `(X, Xᶜ)` and `(X', X'ᶜ)`; we show `X = X'`. Step 1: if `X = X'` the two pairs coincide. Step 2: otherwise the cross-membership property of rectangles puts both mixed pairs `(X, X'ᶜ)` and `(X', Xᶜ)` into `R`, and since `X ≠ X'` the symmetric difference `X ∆ X'` contains some element `i`. Step 3: if `i ∈ X \ X'`, then `i ∈ X ∩ X'ᶜ`, so the mixed pair `(X, X'ᶜ)` is intersecting while the diagonal pair `(X, Xᶜ)` is disjoint; monochromaticity of `R` gives `Disj(X, Xᶜ) = Disj(X, X'ᶜ)`, a contradiction. Step 4: if `i ∈ X' \ X` the same argument applies with the roles of `X` and `X'` exchanged. -/
theorem CommunicationComplexity.Functions.Disjointness.foolingSet_isFoolingSet (n : ℕ) :
    IsFoolingSet (foolingSet n) (disjointness n) := by
  intro R hR hmono p hp q hq
  rcases p with ⟨X, Y⟩
  rcases q with ⟨X', Y'⟩
  simp only [foolingSet, Set.mem_inter_iff, Set.mem_setOf_eq] at hp hq
  rcases hp with ⟨rfl, hpR⟩
  rcases hq with ⟨rfl, hqR⟩
  by_cases hXX' : X = X'
  · -- Step 1: equal sets give the same pair.
    subst hXX'
    rfl
  · -- Step 2: the mixed pairs lie in `R`, and some `i` separates `X` from `X'`.
    have hcross := (IsRectangle_iff R).mp hR X X' Xᶜ X'ᶜ hpR hqR
    obtain ⟨i, hi⟩ : (X ∆ X').Nonempty := Set.symmDiff_nonempty.mpr hXX'
    rw [Set.mem_symmDiff] at hi
    rcases hi with hi | hi
    · -- Step 3: `i ∈ X \ X'`, so `(X, X'ᶜ)` intersects while `(X, Xᶜ)` is disjoint.
      have hval := hmono X X Xᶜ X'ᶜ hpR hcross.2
      have htrue : disjointness n X Xᶜ = true := by
        simpa [disjointness] using (disjoint_compl_right : Disjoint X Xᶜ)
      have hne : disjointness n X X'ᶜ ≠ true := by
        unfold disjointness
        simp only [ne_eq, decide_eq_true_eq]
        intro hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj hi.1 hi.2
      rw [htrue] at hval
      exact (hne hval.symm).elim
    · -- Step 4: `i ∈ X' \ X`, the mirror image with `X` and `X'` exchanged.
      have hval := hmono X' X' X'ᶜ Xᶜ hqR hcross.1
      have htrue : disjointness n X' X'ᶜ = true := by
        simpa [disjointness] using (disjoint_compl_right : Disjoint X' X'ᶜ)
      have hne : disjointness n X' Xᶜ ≠ true := by
        unfold disjointness
        simp only [ne_eq, decide_eq_true_eq]
        intro hdisj
        rw [Set.disjoint_left] at hdisj
        exact hdisj hi.1 hi.2
      rw [htrue] at hval
      exact (hne hval.symm).elim
