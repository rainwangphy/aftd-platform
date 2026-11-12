import AFTD.Prelude

/-!
# base_polytope_submodular

Topic: submodular   Node: ed2120259679

Provenance: formalization of a published result. Source: Fujishige 1980; Schrijver "Combinatorial Optimization" Sec. 44.1

The base polytope B(f) of a set function f on Finset (Fin n) is the set of points x in ℝ^n satisfying ∑_{i ∈ S} x i ≤ f(S) for all subsets S and ∑_{i} x i = f(Finset.univ).
-/

/-- The base polytope B(f) of a set function f on Finset (Fin n). -/
def base_polytope_submodular {n : ℕ} (f : Finset (Fin n) → ℝ) : Set (Fin n → ℝ) := { x | (∀ S : Finset (Fin n), ∑ i ∈ S, x i ≤ f S) ∧ ∑ i : Fin n, x i = f Finset.univ }
