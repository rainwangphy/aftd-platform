import AFTD.Prelude
import AFTD.Kb.Tcs.Op869ScheduleAndInversionImplyThreeColorBound
import AFTD.Kb.Tcs.Op869ThreeColorableBoundImpliesDeterministicLowerBound
import AFTD.Kb.Tcs.IsOnlineColoringAlg
import AFTD.Kb.Tcs.ProperlyColorsKColorable
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.ColorsUsed

/-!
# op869_schedule_and_inversion_imply_deterministic_lower_bound

Topic: online_algorithms   Node: feba6d50f3b8

Provenance: helper lemma. Consequence of the three-colorable lower bound in arXiv:2610.41516 Theorem 1.1 and the previously proved three-colorable-to-k reduction.

If the explicit integer schedule yields the required one-fold adversary games and its budget has the stated logarithmic inversion, then the deterministic online coloring lower bound holds for every k at least four.
-/

/-- Reduce the requested deterministic lower bound to the integer schedule and its asymptotic inversion. -/
theorem op869_schedule_and_inversion_imply_deterministic_lower_bound (C : ℕ)
    (hgame : ∀ m : ℕ, 2 ≤ m → let K := m^m; let F := C*K^3*2^(C*(m+1));
      ∀ n : ℕ, F^(m^2) ≤ n →
      op869_bounded_adversary_forces 3 1 K (F^m) n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅))
    (hasym : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ m : ℕ, 2 ≤ m ∧
        (let K := m^m; let F := C*K^3*2^(C*(m+1)); F^(m^2) ≤ n) ∧
        Real.exp (c * (Real.log (n : ℝ) ^ ((1 : ℝ) / 3)) *
          (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3))) ≤ (m^m : ℝ))
    (k : ℕ) (hk : 4 ≤ k) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ A : SimpleGraph (Fin n) → (Fin n → ℕ), IsOnlineColoringAlg A →
        ProperlyColorsKColorable k A → ∃ G : SimpleGraph (Fin n), G.Colorable k ∧
          Real.exp (c * (Real.log (n : ℝ) ^ ((1 : ℝ) / ((k : ℝ) - 1))) *
            (Real.log (Real.log (n : ℝ)) ^ (((k : ℝ) - 2) / ((k : ℝ) - 1)))) ≤ (colorsUsed (A G) : ℝ) := by
  exact op869_three_colorable_bound_implies_deterministic_lower_bound (op869_schedule_and_inversion_imply_three_color_bound C hgame hasym) k hk
