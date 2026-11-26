import AFTD.Prelude

/-!
# kth_largest

Topic: approximation   Node: 6b9d9569ab7c

Provenance: formalization of a published result. Source: arXiv:2611.30731, Section 2

The $i$-th largest entry of a vector $x : \mathrm{Fin}\,n \to \mathbb{R}$, indexed from 0, padded with 0 if $i \ge n$.
-/

/-- The i-th largest entry of a vector x, with 0-padding. -/
noncomputable def kth_largest {n : ℕ} (x : Fin n → ℝ) (i : ℕ) : ℝ := ((List.ofFn x).mergeSort (· ≥ ·)).getD i 0
