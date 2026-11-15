import AFTD.Prelude

/-!
# kernel_symm

Topic: combinatorics   Node: 4447332d8a17

Provenance: formalization of a published result. Source: arXiv:2611.15027, Section 2

The symmetrization of a kernel W on a host vertex set is defined by (W(x, y) + W(y, x)) / 2.
-/

/-- The symmetrization of a kernel W is (W(x,y) + W(y,x))/2. -/
noncomputable def kernel_symm {H : Type*} (W : H → H → ℝ) : H → H → ℝ := fun x y ↦ (W x y + W y x) / 2
