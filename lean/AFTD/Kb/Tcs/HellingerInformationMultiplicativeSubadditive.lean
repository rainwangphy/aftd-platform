import AFTD.Prelude
import AFTD.Kb.Tcs.HellingerMutualInformation

/-!
# hellinger_information_multiplicative_subadditive

Topic: information   Node: b35412919a8f

Provenance: original. Related work: scout/2610-21231-on-the-subadditivity-of-mutual-f-information.md:123

A real number C satisfies multiplicative subadditivity for Hellinger mutual information if for all finite types X, Y, Z, every prior pX on X and channels PY from X to Y and PZ from X to Z forming a Markov chain Y <- X -> Z (so pXYZ(x, y, z) = pX(x) * PY(x, y) * PZ(x, z)), the joint Hellinger mutual information satisfies hellinger_mutual_information (fun x (yz : Y × Z) => pX x * PY x yz.1 * PZ x yz.2) ≤ C * (hellinger_mutual_information (fun x y => pX x * PY x y) + hellinger_mutual_information (fun x z => pX x * PZ x z)).
-/

/-- Multiplicative subadditivity of Hellinger mutual information with factor C. -/
def hellinger_information_multiplicative_subadditive (C : ℝ) : Prop := ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z]
    (pX : X → ℝ) (PY : X → Y → ℝ) (PZ : X → Z → ℝ),
    (∀ x, 0 ≤ pX x) → (∑ x, pX x = 1) →
    (∀ x y, 0 ≤ PY x y) → (∀ x, ∑ y, PY x y = 1) →
    (∀ x z, 0 ≤ PZ x z) → (∀ x, ∑ z, PZ x z = 1) →
    hellinger_mutual_information (fun x (yz : Y × Z) => pX x * PY x yz.1 * PZ x yz.2) ≤
      C * (hellinger_mutual_information (fun x y => pX x * PY x y) +
           hellinger_mutual_information (fun x z => pX x * PZ x z))
