import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CanForce
import AFTD.Kb.GameTheoryEconomics.IsOmg
import AFTD.Kb.GameTheoryEconomics.PairwiseForcingThreePartitionTypeW
import AFTD.Kb.GameTheoryEconomics.IsOmgOfHasTypeWManipulation

/-!
# obvious_group_manipulation_of_three_forcing_coalitions

Topic: social_choice   Node: 30927ceaf485

Provenance: formalization of a published result. Source: arXiv:2611.26224 Proposition 3

If the voter set N can be partitioned into three nonempty coalitions C1, C2, C3 such that every pairwise union can force each of three distinct alternatives a, b, c, then f is obviously manipulable by groups (OMG).
-/

/-- If the voters can be partitioned into three nonempty sets such that any union of two can force each of three distinct alternatives, then the rule is OMG. -/
theorem obvious_group_manipulation_of_three_forcing_coalitions {N A : Type*} [Fintype N] [DecidableEq N]
    (a b c : A) (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (C1 C2 C3 : Finset N)
    (h1 : C1.Nonempty) (h2 : C2.Nonempty) (h3 : C3.Nonempty)
    (hd12 : Disjoint C1 C2) (hd23 : Disjoint C2 C3) (hd13 : Disjoint C1 C3)
    (hu : C1 ∪ C2 ∪ C3 = Finset.univ)
    (f : (N → LinearOrder A) → A)
    (hf12 : ∀ x ∈ ({a, b, c} : Set A), can_force f (C1 ∪ C2) x)
    (hf23 : ∀ x ∈ ({a, b, c} : Set A), can_force f (C2 ∪ C3) x)
    (hf13 : ∀ x ∈ ({a, b, c} : Set A), can_force f (C1 ∪ C3) x) :
    is_omg f := by
  exact is_omg_of_has_type_w_manipulation f
    (pairwise_forcing_three_partition_type_w a b c hab hbc hac C1 C2 C3 h1 h2 h3 hd12 hd23 hd13 hu f
      hf12 hf23 hf13)
