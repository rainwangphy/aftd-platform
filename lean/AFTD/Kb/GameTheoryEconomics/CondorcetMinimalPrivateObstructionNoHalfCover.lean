import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalPrivateAveragingObstruction
import AFTD.Kb.GameTheoryEconomics.CondorcetDimensionLeThreeIffAcyclicWeightSeparation

/-!
# condorcet_minimal_private_obstruction_no_half_cover

Topic: social_choice   Node: 80f16305e140

Provenance: helper lemma. IN-362 scope check for the eight-vertex minimum-core averaging diagnostic in OP-19. No new election bound or research advance.

The explicit eight-vertex globally minimal averaging obstruction has no integer acyclic half-cover with a positive number of sets. Its failure concerns the uniform averaging construction only.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def condorcet_minimal_private_separator_weight : Fin 8 → ℕ := ![1,1,1,1,4,1,3,4]

theorem condorcet_minimal_private_separator_check : ∀ A : Finset (Fin 8),
    (∀ a ∈ A, ∀ b ∈ A,
      ¬ (condorcet_minimal_private_relation a b ∧ condorcet_minimal_private_relation b a)) →
    (∑ a ∈ A, condorcet_minimal_private_separator_weight a) ≤ 6 := by decide

theorem condorcet_minimal_private_acyclic_weight_bound (A : Finset (Fin 8))
    (hA : WellFounded (fun a b : {a : Fin 8 // a ∈ A} =>
      condorcet_minimal_private_relation a.val b.val)) :
    2 * (∑ a ∈ A, (condorcet_minimal_private_separator_weight a : ℝ)) <
      ∑ a : Fin 8, (condorcet_minimal_private_separator_weight a : ℝ) := by
  have hbound := condorcet_minimal_private_separator_check A (by
    intro a ha b hb ⟨hab,hba⟩
    exact hA.asymmetric (a := ⟨a,ha⟩) (b := ⟨b,hb⟩) hab hba)
  have hreal : (∑ a ∈ A, (condorcet_minimal_private_separator_weight a : ℝ)) ≤ 6 := by
    exact_mod_cast hbound
  have htotal : (∑ a : Fin 8, condorcet_minimal_private_separator_weight a) = 16 := by decide
  have htotalR : (∑ a : Fin 8, (condorcet_minimal_private_separator_weight a : ℝ)) = 16 := by
    exact_mod_cast htotal
  rw [htotalR]
  linarith

theorem condorcet_minimal_private_obstruction_no_half_cover
    (n : ℕ) (U : Fin n → Finset (Fin 8)) (hn : 0 < n)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin 8 // a ∈ U v} =>
      condorcet_minimal_private_relation a.val b.val)) :
    ¬ (∀ a, n ≤ 2 * (univ.filter fun v => a ∈ U v).card) := by
  classical
  intro hhalf
  exact condorcet_half_cover_finite_weighted_half_cover_exclusion 8 n hn U hhalf
    (fun a => (condorcet_minimal_private_separator_weight a : ℝ))
    (fun a => Nat.cast_nonneg _) (fun v => condorcet_minimal_private_acyclic_weight_bound _ (hU v))
