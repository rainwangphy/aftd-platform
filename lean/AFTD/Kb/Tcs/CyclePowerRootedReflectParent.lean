import AFTD.Prelude
import AFTD.Kb.Tcs.CyclePowerRootedReflect

/-!
# cycle_power_rooted_reflect_parent

Topic: combinatorics   Node: eba11f14633c

Provenance: helper lemma. Uniform structural route for OP-205 / RT-1, following arXiv:2610.15635. These are helper reductions, not a proof of the open covering value and not a research advance. The upper-vertical core remains an explicit unproved hypothesis.

Reflection preserves both parent implications at every even rank2q, interchanging the lower and upper branches.
-/

set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

theorem cycle_power_rooted_reflect_parent
    (D q : ℕ) (hq : 0 < q) (hD : 2*q ≤ D) (x : ℤ → ℕ → Bool)
    (hparent : ∀ p a, a < 2*q →
      (a < q → x p (a+D-2*q) = true → x p a = true) ∧
      (q ≤ a → x p a = true → x p (a+D-2*q) = true)) :
    ∀ p a, a < 2*q →
      (a < q → cycle_power_rooted_reflect D x p (a+D-2*q) = true →
        cycle_power_rooted_reflect D x p a = true) ∧
      (q ≤ a → cycle_power_rooted_reflect D x p a = true →
        cycle_power_rooted_reflect D x p (a+D-2*q) = true) := by
  intro p a ha
  let r := -p-((D-1 : ℕ) : ℤ)
  have hi₁ : D-1-(a+D-2*q)=2*q-1-a := by omega
  have hi₂ : (2*q-1-a)+D-2*q=D-1-a := by omega
  constructor
  · intro haq hb
    have hb' : x r (2*q-1-a) = true := by
      simpa only [cycle_power_rooted_reflect,hi₁,r] using hb
    have hh := (hparent r (2*q-1-a) (by omega)).2 (by omega) hb'
    simpa only [cycle_power_rooted_reflect,hi₂,r] using hh
  · intro haq hb
    have hb' : x r ((2*q-1-a)+D-2*q) = true := by
      simpa only [cycle_power_rooted_reflect,hi₂,r] using hb
    have hh := (hparent r (2*q-1-a) (by omega)).1 (by omega) hb'
    simpa only [cycle_power_rooted_reflect,hi₁,r] using hh
