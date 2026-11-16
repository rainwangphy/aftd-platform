import AFTD.Prelude

/-!
# op1370_specialization_distinguishes_fractions

Topic: combinatorics   Node: d9234ca73de7

Provenance: helper lemma.

If a specialization distinguishes two fractions with nonzero denominators, their original cross products differ.
-/

open Finset Matrix Polynomial
open scoped BigOperators

theorem op1370_specialization_distinguishes_fractions
    {R K : Type*} [CommRing R] [Field K] (f : R →+* K) (a b c d : R)
    (hb : f b ≠ 0) (hd : f d ≠ 0)
    (hne : f a / f b ≠ f c / f d) : a * d ≠ c * b := by
  intro he
  apply hne
  apply (div_eq_div_iff hb hd).mpr
  simpa only [map_mul] using congrArg f he
