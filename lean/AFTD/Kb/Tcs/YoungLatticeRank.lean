import AFTD.Prelude
import AFTD.Kb.Tcs.YoungLattice

/-!
# young_lattice_rank

Topic: combinatorics   Node: 007109d49fa0

Provenance: formalization of a published result. Source: arXiv:2610.24148, Section 2.7.4

The centered rank of a Young diagram μ in L(m, n) is 2 * |cells(μ)| - m * n.
-/

/-- The centered rank function on the Young lattice L(m, n), taking values from -m*n to m*n with step size 2. -/
def young_lattice_rank (m n : ℕ) (μ : YoungLattice m n) : ℤ := 2 * (μ.val.cells.card : ℤ) - (m * n : ℤ)
