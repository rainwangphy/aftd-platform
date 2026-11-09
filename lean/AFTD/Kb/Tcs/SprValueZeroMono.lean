import AFTD.Prelude
import AFTD.Kb.Tcs.SprValue
import AFTD.Kb.Optimization.PartialAssignmentLe
import AFTD.Kb.Tcs.SprSignCount

/-!
# spr_value_zero_mono

Topic: learning   Node: eebd732ccc57

Provenance: helper lemma. arXiv:2410.07623, Section 2.2

At horizon 0, the sign-preservation-with-reuse game value equals the sign count, which is monotone under sign deletion: if b' is a sub-board of b (partial_assignment_le b' b), then spr_value n 0 b' ≤ spr_value n 0 b.
-/

/-- Sign deletion monotonicity holds at horizon zero. -/
theorem spr_value_zero_mono (n : ℕ) (b b' : Fin n → Option Bool)
    (hle : partial_assignment_le b' b) :
    spr_value n 0 b' ≤ spr_value n 0 b := by
  change spr_sign_count b' ≤ spr_sign_count b
  unfold spr_sign_count
  apply Finset.card_le_card
  intro i hi
  rw [Finset.mem_filter] at hi ⊢
  refine ⟨hi.1, ?_⟩
  cases h : b' i with
  | none => simp [h] at hi
  | some val =>
    have h_b := hle i val h
    simp [h_b]
