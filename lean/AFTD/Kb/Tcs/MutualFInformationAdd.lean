import AFTD.Prelude
import AFTD.Kb.Tcs.MutualFInformation

/-!
# mutual_f_information_add

Topic: information   Node: d06246c68ae4

Provenance: helper lemma. Helper for the cone and affine-invariance facts about subadditive generators (OP-331).

The mutual f-information is additive in the generator: for any f, h : ℝ → ℝ and any p : X → Y → ℝ on finite types, Ĩ_{f+h}(p) = Ĩ_f(p) + Ĩ_h(p).
-/

theorem mutual_f_information_add {X Y : Type*} [Fintype X] [Fintype Y] (f h : ℝ → ℝ)
    (p : X → Y → ℝ) :
    mutual_f_information (fun t => f t + h t) p =
      mutual_f_information f p + mutual_f_information h p := by
  simp only [mutual_f_information, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl (fun x _ => Finset.sum_congr rfl (fun y _ => by ring))
