import AFTD.Prelude

/-!
# hamming_all_distinct_coords

Topic: combinatorics   Node: 3765ee777910

Provenance: formalization of a published result. Source: arXiv:2610.32789 "Triangle-Free Sets in Exact-Distance Hamming Graphs", Section 2.1

For vectors $x, y, z : \mathrm{Fin}\, n \to \alpha$ over an alphabet $\alpha$ with decidable equality, $\mathrm{hamming\_all\_distinct\_coords}(x, y, z)$ is the set of coordinates $i \in \mathrm{Fin}\, n$ where $x(i), y(i), z(i)$ are pairwise distinct: $x(i) \neq y(i) \wedge x(i) \neq z(i) \wedge y(i) \neq z(i)$.
-/

/-- The set of coordinates where all three vectors x, y, z have pairwise distinct symbols. -/
def hamming_all_distinct_coords {n : ℕ} {α : Type*} [DecidableEq α] (x y z : Fin n → α) : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ y i ∧ x i ≠ z i ∧ y i ≠ z i)
