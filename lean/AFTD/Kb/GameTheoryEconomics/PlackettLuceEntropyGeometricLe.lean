import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PlackettLuceProb
import AFTD.Kb.GameTheoryEconomics.PlackettLuceEntropy
import AFTD.Kb.GameTheoryEconomics.RankingsOfEmpty
import AFTD.Kb.GameTheoryEconomics.PlackettLuceEntropyEq
import AFTD.Kb.GameTheoryEconomics.GeometricFirstChoiceEntropyLe

/-!
# plackett_luce_entropy_geometric_le

Topic: social_choice   Node: 339fd80b5cd1

For geometric weights phi^a with 0 < phi < 1, the Plackett-Luce entropy on any set of n alternatives is at most C(phi) * n with C(phi) = log(1/(1-phi)) + log(1/phi) * phi/(1-phi)^2.
-/

lemma plackett_luce_entropy_geometric_le (φ : ℝ) (h0 : 0 < φ) (h1 : φ < 1) :
    ∀ n (S : Finset ℕ), S.card = n →
      plackett_luce_entropy (fun i => φ ^ i) S ≤
        (Real.log (1 - φ)⁻¹ + (-Real.log φ) * (φ / (1 - φ) ^ 2)) * n := by
  set C := Real.log (1 - φ)⁻¹ + (-Real.log φ) * (φ / (1 - φ) ^ 2)
  intro n
  induction n with
  | zero =>
    intro S hS
    rw [Finset.card_eq_zero.1 hS, plackett_luce_entropy, rankings_of_empty, Finset.sum_singleton,
      plackett_luce_prob]
    simp
  | succ n ih =>
    intro S hS
    have hne : S.Nonempty := Finset.card_pos.1 (by omega)
    have hw : ∀ b ∈ S, 0 < φ ^ b := fun b _ => pow_pos h0 b
    have hW : 0 < ∑ b ∈ S, φ ^ b := Finset.sum_pos hw hne
    rw [plackett_luce_entropy_eq _ S hne hw]
    have hrest : ∑ a ∈ S, φ ^ a / (∑ b ∈ S, φ ^ b) * plackett_luce_entropy (fun i => φ ^ i) (S.erase a)
        ≤ ∑ a ∈ S, φ ^ a / (∑ b ∈ S, φ ^ b) * (C * n) := by
      refine Finset.sum_le_sum fun a ha => ?_
      exact mul_le_mul_of_nonneg_left
        (ih (S.erase a) (by rw [Finset.card_erase_of_mem ha]; omega))
        (div_nonneg (hw a ha).le hW.le)
    rw [← Finset.sum_mul, ← Finset.sum_div, div_self hW.ne', one_mul] at hrest
    have := geometric_first_choice_entropy_le φ h0 h1 S hne
    push_cast
    linarith
