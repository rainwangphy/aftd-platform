import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_winning_set_univ

Topic: social_choice   Node: cd929f7ac9e4

Provenance: helper lemma. sanity check of is_condorcet_winning_set

The set of all candidates is a Condorcet winning set.
-/

theorem condorcet_winning_set_univ {n m : ℕ} (P : Fin n → Equiv.Perm (Fin m)) :
    is_condorcet_winning_set P Finset.univ := by
  intro a ha; exact absurd (Finset.mem_univ a) ha
