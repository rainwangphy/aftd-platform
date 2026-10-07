import AFTD.Prelude

/-!
# multilinear_extension

Topic: submodular   Node: 1c27f6071f8c

Provenance: formalization of a published result. Source: arXiv:2610.07387 (Stronger hardness for submodular maximization subject to a matroid constraint), Sec. 2.1 (multilinear extension)

The multilinear extension F(x) = Σ_S f(S) ∏_{u∈S} x_u ∏_{u∉S} (1 − x_u) of a set function f on {0, …, m−1}.
-/

/-- The multilinear extension `F(x) = ∑_S f(S) ∏_{u ∈ S} x_u ∏_{u ∉ S} (1 - x_u)` of a set function `f` on `Fin m`. -/
def multilinear_extension {m : ℕ} (f : Finset (Fin m) → ℝ) (x : Fin m → ℝ) : ℝ :=
  ∑ S : Finset (Fin m), f S * (∏ u ∈ S, x u) * ∏ u ∈ Sᶜ, (1 - x u)
