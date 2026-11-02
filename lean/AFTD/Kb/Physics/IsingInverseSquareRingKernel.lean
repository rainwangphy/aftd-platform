import AFTD.Prelude

/-!
# ising_inverse_square_ring_kernel

Topic: statistical_mechanics   Node: b1461b10b1dc

Provenance: formalization of a published result. Source: arXiv:2610.39815, Sections 2–4; helper for OP-806.

For a natural-number ring size L and sites i and j in Fin L, use their real-valued indices i.val and j.val: the kernel is 0 if i=j and otherwise is 1 divided by L squared times sin squared of pi times ((i.val:ℝ)-(j.val:ℝ))/L.
-/

noncomputable def ising_inverse_square_ring_kernel (L : ℕ) (i j : Fin L) : ℝ := if i = j then 0 else
    1 / ((L : ℝ)^2 * (Real.sin (Real.pi * ((i.val : ℝ) - (j.val : ℝ)) / L))^2)
