import AFTD.Prelude
import AFTD.Kb.Tcs.IsTSpacedWord
import AFTD.Kb.Tcs.QaryCanonicalSpacedWord

/-!
# op_1503_canonical_spaced_word_is_spaced

Topic: information   Node: 8da9a8f31502

Provenance: helper lemma. knowledgebase, OP-1503

For any natural numbers t, q, and n with t + 1 ≤ q, the canonical spaced word qary_canonical_spaced_word t q n htq is t-spaced.
-/

/-- The canonical periodic word is t-spaced. -/
theorem op_1503_canonical_spaced_word_is_spaced (t q n : ℕ) (htq : t + 1 ≤ q) :
    is_t_spaced_word t (qary_canonical_spaced_word t q n htq) := by
  intro i j hij hjt heq
  have h_val : (qary_canonical_spaced_word t q n htq i).val = (qary_canonical_spaced_word t q n htq j).val := by
    rw [heq]
  dsimp [qary_canonical_spaced_word] at h_val
  have hdvd : t + 1 ∣ j.val - i.val := Nat.ModEq.dvd' h_val
  have hpos : 0 < j.val - i.val := Nat.sub_pos_of_lt hij
  have hle : t + 1 ≤ j.val - i.val := Nat.le_of_dvd hpos hdvd
  omega
