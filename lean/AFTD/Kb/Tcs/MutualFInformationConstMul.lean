import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformation

/-!
# mutual_f_information_const_mul

Topic: information   Node: 759c3091c07e

Provenance: helper lemma. Helper for the cone and affine-invariance facts about subadditive generators (OP-331).

The mutual f-information is homogeneous in the generator: for any real a, f : ℝ → ℝ and p : X → Y → ℝ on finite types, Ĩ_{a f}(p) = a Ĩ_f(p).
-/

theorem mutual_f_information_const_mul {X Y : Type*} [Fintype X] [Fintype Y] (a : ℝ) (f : ℝ → ℝ)
    (p : X → Y → ℝ) :
    mutual_f_information (fun t => a * f t) p = a * mutual_f_information f p := by
  simp only [mutual_f_information, Finset.mul_sum]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))
