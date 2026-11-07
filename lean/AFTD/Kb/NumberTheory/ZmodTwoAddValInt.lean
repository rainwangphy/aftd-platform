import AFTD.Prelude

/-!
# zmod_two_add_val_int

Topic: elementary_number_theory   Node: cc0676a035f1

Provenance: helper lemma. arXiv:2611.02063 Lemma 3.1

For elements $x, y \in \mathbb{F}_2$, viewing their values in $\{0, 1\}$ as integers, the integer value of $x + y$ in $\mathbb{F}_2$ equals $x + y - 2 x y$ in $\mathbb{Z}$.
-/

/-- Over the integers, the value of the sum in ZMod 2 is x + y - 2xy. -/
lemma zmod_two_add_val_int (x y : ZMod 2) :
    ((x + y).val : ℤ) = (x.val : ℤ) + (y.val : ℤ) - 2 * (x.val : ℤ) * (y.val : ℤ) := by
  fin_cases x <;> fin_cases y <;> rfl
