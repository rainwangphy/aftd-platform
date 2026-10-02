import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsWeaklyConsecutive
import AFTD.Kb.NumberTheory.WeaklyConsecutiveFirstDvd
import AFTD.Kb.NumberTheory.WeaklyConsecutiveRev

/-!
# weakly_consecutive_last_dvd

Topic: elementary_number_theory   Node: c5f634429d90

In a weakly consecutive sequence of length k, the last term divides k.
-/

theorem weakly_consecutive_last_dvd {k : ℕ} (σ : Equiv.Perm (Fin k))
    (hσ : is_weakly_consecutive σ) (hk : 0 < k) : (σ ⟨k - 1, by omega⟩ : ℕ) + 1 ∣ k := by
  have h := weakly_consecutive_first_dvd _ (weakly_consecutive_rev σ hσ) hk
  have e : Fin.rev (⟨0, hk⟩ : Fin k) = ⟨k - 1, by omega⟩ := by
    ext; simp [Fin.val_rev]
  simpa [Equiv.trans_apply, Fin.revPerm_apply, e] using h
