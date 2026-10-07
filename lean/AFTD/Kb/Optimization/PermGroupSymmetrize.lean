import AFTD.Prelude

/-!
# perm_group_symmetrize

Topic: submodular   Node: bb1816560f2a

Provenance: formalization of a published result. Source: arXiv:2610.07387 (Stronger hardness for submodular maximization subject to a matroid constraint), Definition 2.2 (x̄)

The symmetrization x̄ = E_{σ∈G}[σ(x)] of a vector x over a group G of permutations of the coordinates, where σ(x)_{σ(u)} = x_u.
-/

/-- The symmetrization `x̄ = E_{σ ∈ G}[σ(x)]` of `x ∈ ℝ^m` over a group `G` of permutations of `Fin m`, where `σ(x)` is `x` with coordinates moved by `σ`: `σ(x)_{σ u} = x_u`. -/
noncomputable def perm_group_symmetrize {m : ℕ} (G : Subgroup (Equiv.Perm (Fin m)))
    (x : Fin m → ℝ) : Fin m → ℝ := by
  classical
  exact fun u => (∑ σ ∈ Finset.univ.filter (· ∈ G), x (σ⁻¹ u)) /
    (Finset.univ.filter (· ∈ G)).card
