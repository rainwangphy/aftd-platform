import AFTD.Prelude
import AFTD.Kb.Tcs.CodewordSupp

/-!
# codeword_supp_zero

Topic: information   Node: 13ef585edf74

Provenance: helper lemma. folklore

The support of the all-zero codeword $0 : \mathrm{Fin}\, n \to \alpha$ is the empty Finset $\emptyset$.
-/

/-- The support of the all-zero codeword is empty. -/
theorem codeword_supp_zero {n : ℕ} {α : Type*} [DecidableEq α] [Zero α] :
    codeword_supp (0 : Fin n → α) = ∅ := by
  simp [codeword_supp]
