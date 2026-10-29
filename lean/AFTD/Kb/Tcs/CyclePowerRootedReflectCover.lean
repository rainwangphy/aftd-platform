import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerRootedReflect

/-!
# cycle_power_rooted_reflect_cover

Topic: combinatorics   Node: b4a29048cda6

Provenance: helper lemma. Uniform structural route for OP-205 / RT-1, following arXiv:2610.15635. These are helper reductions, not a proof of the open covering value and not a research advance. The upper-vertical core remains an explicit unproved hypothesis.

Reflection preserves coverage of every ordinary distance strictly between0 and the arc length.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_rooted_reflect_cover
    (D : ℕ) (hD : 0 < D) (x : ℤ → ℕ → Bool)
    (hcover : ∀ d : ℕ, 1 ≤ d → d < D → ∀ v : ℤ,
      ∃ a : ℕ, a < D-d ∧ x (v-(a : ℤ)) a = true ∧
        x (v-(a : ℤ)) (a+d) = true) :
    ∀ d : ℕ, 1 ≤ d → d < D → ∀ v : ℤ,
      ∃ a : ℕ, a < D-d ∧ cycle_power_rooted_reflect D x (v-(a : ℤ)) a = true ∧
        cycle_power_rooted_reflect D x (v-(a : ℤ)) (a+d) = true := by
  intro d hd hdD v
  obtain ⟨a,ha,hlo,hhi⟩ := hcover d hd hdD (-v-(d : ℤ))
  let b := D-d-1-a
  have hb : b < D-d := by dsimp [b]; omega
  have hi₁ : D-1-b=a+d := by dsimp [b]; omega
  have hi₂ : D-1-(b+d)=a := by dsimp [b]; omega
  have hp : -(v-(b : ℤ))-((D-1 : ℕ) : ℤ) = -v-(d : ℤ)-(a : ℤ) := by
    dsimp [b]; omega
  refine ⟨b,hb,?_,?_⟩
  · simpa only [cycle_power_rooted_reflect,hi₁,hp] using hhi
  · simpa only [cycle_power_rooted_reflect,hi₂,hp] using hlo
