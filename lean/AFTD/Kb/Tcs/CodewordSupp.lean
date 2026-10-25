import AFTD.Prelude

/-!
# codeword_supp

Topic: information   Node: 222ca4d37366

Provenance: formalization of a published result. Source: arXiv:2610.30613, Section 2

The support of a codeword $x : \mathrm{Fin}\, n \to \alpha$ over an alphabet $\alpha$ with decidable equality and zero is the finite set ($\mathrm{Finset}(\mathrm{Fin}\, n)$) of coordinates $i$ such that $x_i \ne 0$, defined by filtering $\mathrm{Finset.univ}$ by $x_i \ne 0$.
-/

/-- The support of a codeword x : Fin n → α is the Finset of coordinate indices where x is nonzero. -/
def codeword_supp {n : ℕ} {α : Type*} [DecidableEq α] [Zero α] (x : Fin n → α) : Finset (Fin n) := Finset.univ.filter (fun i => x i ≠ 0)
