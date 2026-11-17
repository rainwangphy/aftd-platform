import AFTD.Prelude
import AFTD.Kb.Tcs.Op869BoundedAdversaryForcesUnbounded
import AFTD.Kb.Tcs.Op869AdversaryForcesSound
import AFTD.Kb.Tcs.IsOnlineColoringAlg
import AFTD.Kb.Tcs.ProperlyColorsKColorable
import AFTD.Kb.Tcs.ColorsUsed
import AFTD.Kb.Tcs.Op869GraphFromPredecessors
import AFTD.Kb.Tcs.Op869BoundedAdversaryForces
import AFTD.Kb.Tcs.Op869AdversaryForces

/-!
# op869_schedule_and_inversion_imply_three_color_bound

Topic: online_algorithms   Node: 8e9a26309890

Provenance: helper lemma. arXiv:2610.41516 Section 2.3, using the finite adversary soundness formalization.

If the integer schedule forces its target at every admissible board size and the integer budget has the required logarithmic inversion, then the three-colorable online coloring lower bound follows.
-/

/-- Turn the conditional fold schedule into the three-colorable online lower bound. -/
theorem op869_schedule_and_inversion_imply_three_color_bound (C : ℕ)
    (hgame : ∀ m : ℕ, 2 ≤ m → let K := m^m; let F := C*K^3*2^(C*(m+1));
      ∀ n : ℕ, F^(m^2) ≤ n →
      op869_bounded_adversary_forces 3 1 K (F^m) n 0 (fun _ : Fin n => ∅) (fun _ : Fin n => ∅))
    (hasym : ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∃ m : ℕ, 2 ≤ m ∧
        (let K := m^m; let F := C*K^3*2^(C*(m+1)); F^(m^2) ≤ n) ∧
        Real.exp (c * (Real.log (n : ℝ) ^ ((1 : ℝ) / 3)) *
          (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3))) ≤ (m^m : ℝ)) :
    ∃ c : ℝ, 0 < c ∧ ∃ n₀ : ℕ, ∀ n : ℕ, n₀ ≤ n →
      ∀ A : SimpleGraph (Fin n) → (Fin n → ℕ),
        IsOnlineColoringAlg A → ProperlyColorsKColorable 3 A →
          ∃ G : SimpleGraph (Fin n), G.Colorable 3 ∧
            Real.exp (c * (Real.log (n : ℝ) ^ ((1 : ℝ) / 3)) *
              (Real.log (Real.log (n : ℝ)) ^ ((2 : ℝ) / 3))) ≤ (colorsUsed (A G) : ℝ) := by
  obtain ⟨c, hc, n₀, hasym⟩ := hasym
  refine ⟨c, hc, n₀, ?_⟩
  intro n hn A hA hproper
  obtain ⟨m, hm, hbudget, hbound⟩ := hasym n hn
  let K := m^m
  let F := C*K^3*2^(C*(m+1))
  have hwin : op869_bounded_adversary_forces 3 1 K (F^m) n 0
      (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) := hgame m hm n hbudget
  have hplay := op869_bounded_adversary_forces_unbounded 3 1 K (F^m) n 0
    (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) hwin
  obtain ⟨G, hcolor, hused⟩ := op869_adversary_forces_sound 3 K A hA hproper n 0
    (fun _ : Fin n => ∅) (fun _ : Fin n => ∅) hplay (by intro a ha; omega)
  refine ⟨G, hcolor, le_trans hbound ?_⟩
  exact_mod_cast hused
