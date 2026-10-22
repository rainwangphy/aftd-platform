import AFTD.Prelude

/-!
# sum_comp_neg

Topic: combinatorics   Node: 741ae33072a6

Provenance: helper lemma. helper for arXiv:2610.27175 Theorem 5

For v : Fin m → ℤ with m > 0, the sum of v(-j) over j equals the sum of v.
-/

theorem sum_comp_neg {m : ℕ} [NeZero m] (v : Fin m → ℤ) : ∑ j, v (-j) = ∑ j, v j :=
  Fintype.sum_equiv (Equiv.neg _) _ _ (fun _ => rfl)
