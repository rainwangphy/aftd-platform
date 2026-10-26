import AFTD.Prelude

/-!
# complex_laplacian_sector_cost

Topic: graphs   Node: bef1faa25a55

Provenance: helper lemma. Sector-bound formalization for IN-166; arXiv:math/0508176, Theorem 5.

The sum of the real and imaginary parts of the complex Laplacian edge form.
-/

def complex_laplacian_sector_cost (u v : ℂ) : ℝ := u.re * (u.re - v.re) + u.im * (u.im - v.im) +
    u.re * (u.im - v.im) - u.im * (u.re - v.re)
