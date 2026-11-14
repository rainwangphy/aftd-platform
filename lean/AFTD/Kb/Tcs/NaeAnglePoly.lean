import AFTD.Prelude

/-!
# nae_angle_poly

Topic: quantum   Node: a785cba1bb53

Provenance: original. Related work: Explicit polynomial certificate for the p-computation rule analysis in arXiv:1211.0721, Section 3.3.

The real-valued function nae_angle_poly is defined for real x by 9(16x²−20x+5)²−128x(1−x)²(3−4x)⁴(1−4x)⁴.
-/

noncomputable def nae_angle_poly (x : ℝ) : ℝ :=
  9 * (16 * x ^ 2 - 20 * x + 5) ^ 2 -
    128 * x * (1 - x) ^ 2 * (3 - 4 * x) ^ 4 * (1 - 4 * x) ^ 4
