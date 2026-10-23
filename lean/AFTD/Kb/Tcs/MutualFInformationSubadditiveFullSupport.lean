import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformation

/-!
# mutual_f_information_subadditive_full_support

Topic: information   Node: 4e01a3f6b320

Provenance: formalization of a published result. Source: arXiv:2610.21231 (On the subadditivity of mutual f-information), Definition 1, restricted to full-support distributions: the proof of Theorem 1 (Appendix B) first reduces to this case by continuity. The restriction is needed for generators such as those of Corollary 1, which are +∞ at 0 (f: [0, ∞) → ℝ ∪ {+∞} in Definition 1), a value a real-valued Lean f cannot take.

Subadditivity of mutual f-information on full-support distributions: for all finite X, Y, Z, every p_X > 0 and channels p_{Y|X} > 0, p_{Z|X} > 0, the Markov chain Y → X → Z (p_{XYZ} = p_X p_{Y|X} p_{Z|X}) satisfies Ĩ_f(X; YZ) ≤ Ĩ_f(X; Y) + Ĩ_f(X; Z). Only the values of f on (0, ∞) enter.
-/

def mutual_f_information_subadditive_full_support (f : ℝ → ℝ) : Prop :=
  ∀ (X Y Z : Type) [Fintype X] [Fintype Y] [Fintype Z]
    (pX : X → ℝ) (PY : X → Y → ℝ) (PZ : X → Z → ℝ),
    (∀ x, 0 < pX x) → (∑ x, pX x = 1) →
    (∀ x y, 0 < PY x y) → (∀ x, ∑ y, PY x y = 1) →
    (∀ x z, 0 < PZ x z) → (∀ x, ∑ z, PZ x z = 1) →
    mutual_f_information f (fun x (yz : Y × Z) => pX x * PY x yz.1 * PZ x yz.2) ≤
      mutual_f_information f (fun x y => pX x * PY x y) +
        mutual_f_information f (fun x z => pX x * PZ x z)
