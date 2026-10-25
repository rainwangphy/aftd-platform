import AFTD.Prelude
import AFTD.Kb.Tcs.CodewordSupp

/-!
# four_supports

Topic: information   Node: d1c909356d84

Provenance: formalization of a published result. Source: arXiv:2610.30613, Section 3, equation (9)

The family of four-supports of a code $\mathcal{C} \subseteq (\mathrm{Fin}\, n \to \alpha)$ is the set of all Finsets $S : \mathrm{Finset}(\mathrm{Fin}\, n)$ such that $S = \mathrm{codeword\_supp}(x)$ for some codeword $x \in \mathcal{C}$ with cardinality $(\mathrm{codeword\_supp}(x)).\mathrm{card} = 4$.
-/

/-- The family of four-supports of codewords of weight 4 in a code C. -/
def four_supports {n : ℕ} {α : Type*} [DecidableEq α] [Zero α] (C : Set (Fin n → α)) : Set (Finset (Fin n)) := {S | ∃ x ∈ C, (codeword_supp x).card = 4 ∧ codeword_supp x = S}
