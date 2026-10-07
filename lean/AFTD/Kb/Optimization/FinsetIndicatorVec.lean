import AFTD.Prelude

/-!
# finset_indicator_vec

Topic: submodular   Node: 40640678fe9e

Provenance: formalization of a published result. Source: arXiv:2610.07387 (Stronger hardness for submodular maximization subject to a matroid constraint), Sec. 2.2

The indicator vector 1_S ∈ ℝ^m of a set S ⊆ {0, …, m−1}.
-/

/-- The indicator vector `1_S ∈ ℝ^m` of `S ⊆ Fin m`. -/
def finset_indicator_vec {m : ℕ} (S : Finset (Fin m)) : Fin m → ℝ :=
  fun u => if u ∈ S then 1 else 0
