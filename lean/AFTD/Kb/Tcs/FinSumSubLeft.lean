import AFTD.Prelude

/-!
# fin_sum_sub_left

Topic: combinatorics   Node: e460f3e2942b

Provenance: helper lemma. helper for arXiv:2610.27175 Theorem 5

For v : Fin m → ℤ with m > 0 and any i, the sum of v(i - j) over j equals the sum of v.
-/

theorem fin_sum_sub_left {m : ℕ} [NeZero m] (v : Fin m → ℤ) (i : Fin m) :
    ∑ j, v (i - j) = ∑ j, v j :=
  Fintype.sum_equiv (Equiv.subLeft i) _ _ (fun _ => rfl)
