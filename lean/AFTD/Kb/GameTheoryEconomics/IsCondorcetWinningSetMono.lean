import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# is_condorcet_winning_set_mono

Topic: social_choice   Node: b6576cefa23e

Provenance: original. Related work: folklore

Condorcet winning sets are upward closed: if S is a Condorcet winning set and S is a subset of T, then T is also a Condorcet winning set.
-/

/-- Monotonicity of Condorcet winning sets: any superset of a Condorcet winning set is also a Condorcet winning set. -/
theorem is_condorcet_winning_set_mono {n m : ℕ} (P : Fin n → Equiv.Perm (Fin m))
    {S T : Finset (Fin m)} (hS : is_condorcet_winning_set P S) (hST : S ⊆ T) :
    is_condorcet_winning_set P T := by
  intro a ha
  have haS : a ∉ S := fun h => ha (hST h)
  have hScard := hS a haS
  have hsub : (Finset.univ.filter fun v => ∀ b ∈ T, P v a < P v b) ⊆
              (Finset.univ.filter fun v => ∀ b ∈ S, P v a < P v b) := by
    intro v hv
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hv ⊢
    intro b hb
    exact hv b (hST hb)
  have hcard_le := Finset.card_le_card hsub
  linarith
