import AFTD.Prelude
import AFTD.Kb.NumberTheory.HyperbinaryLengthPoly

/-!
# hyperbinaryCountMod3

Topic: elementary_number_theory   Node: 7bdf8f409c74

Provenance: formalization of a published result. Source: scout/2611-01243-halving-partitions-and-hyperbinary-expansions.md:1191

For nonnegative integers m and r, hyperbinaryCountMod3 m r is the sum of coefficients of the hyperbinary length polynomial H_m(z) over exponents j with j % 3 = r % 3.
-/

/-- The count N_r(m) of hyperbinary expansions of m of length congruent to r mod 3. -/
noncomputable def hyperbinaryCountMod3 (m : ℕ) (r : ℕ) : ℤ := Finset.sum ((hyperbinaryLengthPoly m).support.filter (fun j => j % 3 = r % 3))
    (fun j => (hyperbinaryLengthPoly m).coeff j)
