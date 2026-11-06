import AFTD.Prelude
import AFTD.Kb.Tcs.FullReedSolomonCode

/-!
# zero_mem_full_reed_solomon_code

Topic: information   Node: e248525f979b

Provenance: helper lemma. arXiv:2611.07607

For any commutative ring $F$ and natural number $k$, the constant zero function is a codeword in the full-length Reed-Solomon code of dimension $k$ over $F$.
-/

/-- The all-zero word is in the full-length Reed-Solomon code of any dimension. -/
theorem zero_mem_full_reed_solomon_code (F : Type*) [CommRing F] (k : ℕ) :
    (fun _ : F => (0 : F)) ∈ full_reed_solomon_code F k := by
  dsimp [full_reed_solomon_code]
  exact ⟨0, by rw [Polynomial.degree_zero]; exact WithBot.bot_lt_coe k, by simp⟩
