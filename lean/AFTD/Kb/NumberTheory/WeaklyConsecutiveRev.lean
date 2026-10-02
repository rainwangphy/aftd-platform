import AFTD.Prelude
import AFTD.Kb.NumberTheory.IsWeaklyConsecutive

/-!
# weakly_consecutive_rev

Topic: elementary_number_theory   Node: c880942f9b78

Reading a weakly consecutive sequence backwards gives a weakly consecutive sequence.
-/

theorem weakly_consecutive_rev {k : ℕ} (σ : Equiv.Perm (Fin k))
    (hσ : is_weakly_consecutive σ) : is_weakly_consecutive (Fin.revPerm.trans σ) := by
  intro m i j h hij
  simp only [Equiv.trans_apply, Fin.revPerm_apply] at h ⊢
  apply hσ m (Fin.rev i) (Fin.rev j) h
  have hi := i.isLt
  have hj := j.isLt
  have e : ((Fin.rev i : ℕ) : ℤ) - ((Fin.rev j : ℕ) : ℤ) = -((i : ℤ) - (j : ℤ)) := by
    simp only [Fin.val_rev]
    omega
  rw [e]
  exact (dvd_neg).2 hij
