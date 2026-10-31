import AFTD.Prelude

/-!
# avg_pairwise_hamming_dist

Topic: combinatorics   Node: 5687e5694a43

Provenance: formalization of a published result. Source: arXiv:2610.40486 Sec. 1

For an implicit dimension $n$ and a finite subset $F : \mathrm{Finset} (\mathrm{Fin}\ n \to \mathrm{Bool})$, the average pairwise Hamming distance `avg_pairwise_hamming_dist F` is the real number given by the sum over all pairs $x, y \in F$ of Mathlib's Hamming distance `hammingDist x y` cast to $\mathbb{R}$, divided by $(|F| : \mathbb{R})^2$.
-/

/-- The average pairwise Hamming distance of a finite subset `F` of the Boolean hypercube `Fin n → Bool`. -/
noncomputable def avg_pairwise_hamming_dist {n : ℕ} (F : Finset (Fin n → Bool)) : ℝ := (∑ x ∈ F, ∑ y ∈ F, (hammingDist x y : ℝ)) / (F.card : ℝ)^2
