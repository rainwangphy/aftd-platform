import AFTD.Prelude

/-!
# qutrit_ppt_line_distance_exact

Topic: quantum   Node: 920c27f73ee7

Provenance: helper lemma. OP-2299, finite bound for perturbations vanishing on a Bell line.

If three real coefficients are at most one third and the total with an outside mass is one, their total distance from the uniform line plus outside mass is twice that outside mass.
-/

theorem qutrit_ppt_line_distance_exact (p0 p1 p2 q : ℝ)
    (h0 : p0 ≤ 1/3) (h1 : p1 ≤ 1/3) (h2 : p2 ≤ 1/3)
    (hs : p0+p1+p2+q=1) :
    |p0-1/3| + |p1-1/3| + |p2-1/3| + q = 2*q := by
  rw [abs_of_nonpos (sub_nonpos.mpr h0), abs_of_nonpos (sub_nonpos.mpr h1),
      abs_of_nonpos (sub_nonpos.mpr h2)]
  linarith
