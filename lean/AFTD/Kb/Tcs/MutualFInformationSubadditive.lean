import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformation

/-!
# mutual_f_information_subadditive

Topic: information   Node: f3937c598610

Provenance: formalization of a published result. Source: arXiv:2610.21231, Definition 1

A function f is a subadditive generator for mutual f-information if for all finite random variables X, Y, Z forming a Markov chain Y -> X -> Z (p_{XYZ} = p_X p_{Y|X} p_{Z|X}), the mutual f-information satisfies Ĩ_f(X; YZ) ≤ Ĩ_f(X; Y) + Ĩ_f(X; Z).
-/

/-- Subadditivity of mutual f-information under conditionally independent observations Y -> X -> Z. -/
def mutual_f_information_subadditive (f : ℝ → ℝ) : Prop := ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z]
    (pX : X → ℝ) (PY : X → Y → ℝ) (PZ : X → Z → ℝ),
    (∀ x, 0 ≤ pX x) → (∑ x, pX x = 1) →
    (∀ x y, 0 ≤ PY x y) → (∀ x, ∑ y, PY x y = 1) →
    (∀ x z, 0 ≤ PZ x z) → (∀ x, ∑ z, PZ x z = 1) →
    mutual_f_information f (fun x (yz : Y × Z) => pX x * PY x yz.1 * PZ x yz.2) ≤
      mutual_f_information f (fun x y => pX x * PY x y) +
        mutual_f_information f (fun x z => pX x * PZ x z)
