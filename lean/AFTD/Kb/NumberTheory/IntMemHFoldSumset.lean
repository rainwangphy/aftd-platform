import AFTD.Prelude

/-!
# int_mem_h_fold_sumset

Topic: elementary_number_theory   Node: 6026c7bbfaf1

Provenance: formalization of a published result. Source: arXiv:2610.19470 (Positivity and negativity for h-bases for n), Sec. 1 (the sumset hA).

m belongs to the h-fold sumset hA: m is a sum of exactly h, not necessarily distinct, elements of A.
-/

/-- `m ∈ hA`: `m` is the sum of `h` (not necessarily distinct) elements of the finite set `A ⊆ ℤ`. -/
def int_mem_h_fold_sumset (h : ℕ) (A : Finset ℤ) (m : ℤ) : Prop :=
  ∃ f : Fin h → ℤ, (∀ i, f i ∈ A) ∧ ∑ i, f i = m
