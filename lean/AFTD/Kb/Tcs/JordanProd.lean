import AFTD.Prelude

/-!
# jordan_prod

Topic: quantum   Node: d838456e9828

Provenance: formalization of a published result. Source: arXiv:2610.34972 eq. (1)

For a finite type n and two n × n complex matrices A and B, jordan_prod A B is the complex matrix (1 / 2 : ℂ) • (A * B + B * A).
-/

/-- The Jordan product of two complex matrices indexed by a finite type n: (1/2) * (A * B + B * A). -/
noncomputable def jordan_prod {n : Type*} [Fintype n] (A B : Matrix n n ℂ) : Matrix n n ℂ := (1 / 2 : ℂ) • (A * B + B * A)
