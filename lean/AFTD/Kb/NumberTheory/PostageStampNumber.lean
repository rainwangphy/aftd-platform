import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset
import AFTD.Kb.NumberTheory.PostageStampBasisRange

/-!
# postage_stamp_number

Topic: elementary_number_theory   Node: abcf7a624c8a

Provenance: formalization of a published result. Source: arXiv:2610.19470 (Positivity and negativity for h-bases for n), Sec. 1 (the classical postage stamp problem, n_h(k)).

The postage stamp number n_h(k): the largest n_h(A) over sets A of k + 1 nonnegative integers.
-/

/-- `n_h(k)`: the largest `n_h(A)` over `(k+1)`-element sets `A` of nonnegative integers. -/
noncomputable def postage_stamp_number (h k : ℕ) : ℕ :=
  sSup {n | ∃ A : Finset ℤ, A.card = k + 1 ∧ (∀ a ∈ A, 0 ≤ a) ∧ postage_stamp_basis_range h A = n}
