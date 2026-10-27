import AFTD.Prelude
import AFTD.Kb.Tcs.DiffersAtOne

/-!
# differs_at_one_symm

Topic: combinatorics   Node: d008fab7021c

Provenance: helper lemma. arXiv:2610.03808 Sec. 2.1

For any type ι and any functions f, g : ι → ℤˣ taking values in the units of ℤ, if differs_at_one f g holds, then differs_at_one g f holds.
-/

/-- Symmetry of differing at exactly one index. -/
theorem differs_at_one_symm {ι : Type*} {f g : ι → ℤˣ} (h : differs_at_one f g) : differs_at_one g f := by
  rw [differs_at_one] at *
  obtain ⟨i, hi, huniq⟩ := h
  exact ⟨i, fun hii => hi hii.symm, fun j hj => huniq j hj.symm⟩
