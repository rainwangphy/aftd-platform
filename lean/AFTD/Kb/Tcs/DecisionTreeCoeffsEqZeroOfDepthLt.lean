import AFTD.Prelude
import AFTD.Kb.Tcs.DecisionTree
import AFTD.Kb.Tcs.DecisionTreeDepth
import AFTD.Kb.Tcs.DecisionTreeCoeffs
import AFTD.Kb.Tcs.DecisionTreeCardSymmDiffSingleton

/-!
# DecisionTree.coeffs_eq_zero_of_depth_lt

Topic: circuits   Node: 09561cf59ba2

Provenance: helper lemma. TCSlib, `DecisionTree.coeffs_eq_zero_of_depth_lt`. Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

Fourier coefficients vanish above the tree depth. Let $T$ be a decision tree on $n$ Boolean variables, and let $S \subseteq
\{0,1,\dots,n-1\}$ be a set of variables whose cardinality $\abs{S}$ exceeds the depth
of $T$. Then the coefficient assigned to the frequency $S$ vanishes,
$\mathrm{coeffs}\,T\,S = 0$.
-/

open BooleanAnalysis in
variable {n : ℕ} in
/-- Frequencies above the depth carry no Fourier weight. -/
lemma DecisionTree.coeffs_eq_zero_of_depth_lt (T : DecisionTree n) (S : Finset (Fin n))
    (h : T.depth < S.card) : T.coeffs S = 0 := by
  induction T generalizing S with
  | leaf b =>
      have hS : S ≠ ∅ := by
        intro hS
        rw [hS] at h
        simp [DecisionTree.depth] at h
      simp [coeffs, hS]
  | branch i lo hi ih_lo ih_hi =>
      simp only [DecisionTree.depth] at h
      have hSi := card_symmDiff_singleton S i
      rw [coeffs, ih_lo _ (by omega), ih_hi _ (by omega),
        ih_lo _ (by omega), ih_hi _ (by omega)]
      ring
