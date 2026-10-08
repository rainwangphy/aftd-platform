import AFTD.Prelude
import AFTD.Kb.Tcs.DecisionTreeSymmDiffSingletonInvol

/-!
# DecisionTree.sum_symmDiff_reindex

Topic: circuits   Node: 5bdce54e9fec

Provenance: helper lemma. TCSlib, `DecisionTree.sum_symmDiff_reindex`. Lean proof by Hydroxyi, Owen McGinty, Seyoon Ragavan (from the file's git history), from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/LMN/DecisionTreeFourier.lean (Apache-2.0); 1 verbatim; compiled here.

Invariance of a subset-sum under symmetric difference with a point. Fix $n \in \bbn$, let $i$ be an element of $\{0, 1, \dots, n-1\}$, and let $g$ assign a
real number to each subset of $\{0, 1, \dots, n-1\}$. Then summing $g$ over all subsets
is unaffected by first toggling the membership of $i$; that is,
\[
\sum_{S} g\big(S \mathbin{\triangle} \{i\}\big) = \sum_{S} g(S),
\]
where both sums range over all subsets $S \subseteq \{0, 1, \dots, n-1\}$ and $S
\mathbin{\triangle} \{i\}$ denotes the symmetric difference of $S$ with the singleton
$\{i\}$.
-/

variable {n : ℕ} in
/-- Reindexing a sum over all frequencies by the involution `S ↦ S ∆ {i}`. -/
lemma DecisionTree.sum_symmDiff_reindex (g : Finset (Fin n) → ℝ) (i : Fin n) :
    ∑ S : Finset (Fin n), g (symmDiff S {i}) = ∑ S : Finset (Fin n), g S :=
  Fintype.sum_bijective _ ((symmDiff_singleton_invol i).bijective) _ _ (fun _ => rfl)
