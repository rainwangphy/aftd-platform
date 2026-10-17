import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampBasisRange

/-!
# postage_stamp_number_neg

Topic: elementary_number_theory   Node: 078746cb2372

Provenance: formalization of a published result. Source: arXiv:2610.19470 (Positivity and negativity for h-bases for n), Sec. 1 (n♭_h(k)).

n♭_h(k): the largest n_h(A) over sets A of k + 1 integers containing at least one negative integer.
-/

/-- `n♭_h(k)`: the largest `n_h(A)` over `(k+1)`-element sets `A ⊆ ℤ` with a negative element. -/
noncomputable def postage_stamp_number_neg (h k : ℕ) : ℕ :=
  sSup {n | ∃ A : Finset ℤ, A.card = k + 1 ∧ (∃ a ∈ A, a < 0) ∧ postage_stamp_basis_range h A = n}
