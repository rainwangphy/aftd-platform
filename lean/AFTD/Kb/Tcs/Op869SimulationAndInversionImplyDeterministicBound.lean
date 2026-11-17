import AFTD.Prelude
import AFTD.Kb.Tcs.Op869IntegerFoldScheduleConditional
import AFTD.Kb.Tcs.Op869ScheduleAndInversionImplyDeterministicLowerBound
import AFTD.Kb.Tcs.IsOnlineColoringAlg
import AFTD.Kb.Tcs.ProperlyColorsKColorable
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.ColorsUsed

/-!
# op869_simulation_and_inversion_imply_deterministic_bound

Topic: online_algorithms   Node: d38942a77257

Provenance: helper lemma. The construction and inversion in arXiv:2610.41516 Theorem 1.1 and Lemma 2.5, expressed in the finite bounded-adversary game.

For any positive integer C, the requested deterministic online-coloring lower bound follows for all k≥4 if the stated C-fold simulation inequality and the explicit integer-budget logarithmic inversion both hold.
-/

/-- Reduce the deterministic lower bound to the fold simulation and integer-budget inversion. -/
theorem op869_simulation_and_inversion_imply_deterministic_bound (C : ℕ) (hC : 1 ≤ C)
    (hsim : ∀ n q t K D : ℕ, 1 ≤ t → t ≤ q → q ≤ K → 1 ≤ D →
      op869_bounded_adversary_forces 3 q K D n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) →
      ∀ n' D' : ℕ,
      C * K^2 * q * n * D * 2^(C * ((q + t - 1) / t)) ≤ n' →
      C * K^2 * q * D * 2^(C * ((q + t - 1) / t)) ≤ D' →
      op869_bounded_adversary_forces 3 t K D' n' 0 (fun _ : Fin n' => ∅) (fun _ : Fin n' => ∅))
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
  have hgame : ∀ m : ℕ, 2 ≤ m → let K := m^m; let F := C*K^3*2^(C*(m+1));
      ∀ n : ℕ, F^(m^2) ≤ n →
      op869_bounded_adversary_forces 3 1 K (F^m) n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) := by
    intro m hm
    exact op869_integer_fold_schedule_conditional C m hC hm hsim
  exact op869_schedule_and_inversion_imply_deterministic_lower_bound C hgame hasym k hk
