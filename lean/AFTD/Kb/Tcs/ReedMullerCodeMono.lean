import AFTD.Prelude
import AFTD.Kb.Tcs.ReedMullerCode
import AFTD.Kb.Tcs.Monomial

/-!
# reed_muller_code_mono

Topic: information   Node: b88c0a41cc99

Provenance: helper lemma. folklore

For any natural numbers r1, r2, and s such that r1 ≤ r2, the Reed-Muller code reed_muller_code r1 s is a submodule of reed_muller_code r2 s.
-/

/-- Monotonicity of Reed-Muller codes: RM(r1, s) is contained in RM(r2, s) when r1 ≤ r2. -/
theorem reed_muller_code_mono {r1 r2 s : ℕ} (h : r1 ≤ r2) :
    reed_muller_code r1 s ≤ reed_muller_code r2 s := by
  unfold reed_muller_code
  apply Submodule.span_mono
  intro f hf
  obtain ⟨T, hT, rfl⟩ := hf
  exact ⟨T, le_trans hT h, rfl⟩
