import AFTD.Prelude

/-!
# hamming_exceptional_coords

Topic: combinatorics   Node: d6747c0fe74e

Provenance: formalization of a published result. Source: arXiv:2610.32789 "Triangle-Free Sets in Exact-Distance Hamming Graphs", Section 2.1

For vectors $x, y, z : \mathrm{Fin}\, n \to \alpha$ over an alphabet $\alpha$ with decidable equality, $\mathrm{hamming\_exceptional\_coords}(x, y, z)$ is the set of coordinates $i \in \mathrm{Fin}\, n$ where $x$ is exceptional, meaning $y(i) = z(i)$ and $x(i) \neq y(i)$.
-/

/-- The set of coordinates where the first vector x is exceptional among (x, y, z): y i = z i and x i ≠ y i. -/
def hamming_exceptional_coords {n : ℕ} {α : Type*} [DecidableEq α] (x y z : Fin n → α) : Finset (Fin n) := Finset.univ.filter (fun i => y i = z i ∧ x i ≠ y i)
