import AFTD.Prelude
import AFTD.Kb.NumberTheory.IntMemHFoldSumset

/-!
# postage_stamp_basis_range

Topic: elementary_number_theory   Node: dd4b52749657

Provenance: formalization of a published result. Source: arXiv:2610.19470 (Positivity and negativity for h-bases for n), Sec. 1 (n_h(A)).

n_h(A): the largest n such that every integer in [0, n] belongs to hA (A is an h-basis for n).
-/

/-- `n_h(A)`: the largest `n` with `[0, n] ⊆ hA`. The set of such `n` is bounded since `hA` is finite; it is `0` (not `-1`) when `0 ∉ hA`, which only matters for sets that are no basis at all. -/
noncomputable def postage_stamp_basis_range (h : ℕ) (A : Finset ℤ) : ℕ :=
  sSup {n : ℕ | ∀ m : ℕ, m ≤ n → int_mem_h_fold_sumset h A m}
