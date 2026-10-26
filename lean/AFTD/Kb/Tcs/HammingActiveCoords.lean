import AFTD.Prelude

/-!
# hamming_active_coords

Topic: combinatorics   Node: a80c9925cfc1

Provenance: formalization of a published result. Source: arXiv:2610.32789 "Triangle-Free Sets in Exact-Distance Hamming Graphs", Definition 2.1

For vectors $x, y, z : \mathrm{Fin}\, n \to \alpha$ over an alphabet $\alpha$ with decidable equality, $\mathrm{hamming\_active\_coords}(x, y, z)$ is the set of coordinates $i \in \mathrm{Fin}\, n$ such that $\neg(x(i) = y(i) \wedge y(i) = z(i))$, i.e., where $x(i), y(i), z(i)$ are not all equal.
-/

/-- The set of active coordinates for three vectors x, y, z in an alphabet α: coordinates where their entries are not all equal. -/
def hamming_active_coords {n : ℕ} {α : Type*} [DecidableEq α] (x y z : Fin n → α) : Finset (Fin n) := Finset.univ.filter (fun i => ¬(x i = y i ∧ y i = z i))
