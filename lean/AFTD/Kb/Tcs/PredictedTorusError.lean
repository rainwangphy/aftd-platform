import AFTD.Prelude
import AFTD.Kb.Tcs.BoolAnfCoefficient
import AFTD.Kb.Tcs.BoolNextToTopAnfCount

/-!
# predictedTorusError

Topic: circuits   Node: 1ebefd447b74

Provenance: original. Related work: arXiv:2610.19174, Majority and Torus Polynomials: Bounded-Lift Lower Bounds and Explicit Constructions

For a natural number n and Boolean function f : (Fin n → Bool) → Bool on n variables, predictedTorusError n f is the real error: 1 / (2 * Nat.choose n (n / 2)) if boolAnfCoefficient f Finset.univ is true; 0 if boolAnfCoefficient f Finset.univ is false and boolNextToTopAnfCount f = 0; and 1 / (2^(n - h) * Nat.choose h (h / 2)) where h = min (boolNextToTopAnfCount f - 1) (n - boolNextToTopAnfCount f) if boolAnfCoefficient f Finset.univ is false and boolNextToTopAnfCount f > 0.
-/

/-- Predicted optimal degree-(n-2) torus approximation error from top two ANF layers. -/
noncomputable def predictedTorusError (n : ℕ) (f : (Fin n → Bool) → Bool) : ℝ := if boolAnfCoefficient f Finset.univ then
    1 / (2 * (n.choose (n / 2) : ℝ))
  else
    let k := boolNextToTopAnfCount f
    if k = 0 then
      0
    else
      let h := min (k - 1) (n - k)
      1 / ((2 : ℝ) ^ (n - h) * (h.choose (h / 2) : ℝ))
