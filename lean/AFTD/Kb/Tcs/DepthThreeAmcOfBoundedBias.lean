import AFTD.Prelude
import AFTD.Kb.Tcs.HasDepthThreeAmcBoundedBiasProof
import AFTD.Kb.Tcs.HasDepthThreeAmcProof
import AFTD.Kb.Tcs.IsRankOneProduct
import AFTD.Kb.Tcs.CnfLit

/-!
# depth_three_amc_of_bounded_bias

Topic: proof_complexity   Node: 57de8b4bfd74

Provenance: formalization of a published result. Source: arXiv:2611.01055, Section 2.3, page 23

For every natural number n, every DNF formula A : List (List (CnfLit (Fin n))), every real shift parameter ε, and every proof size s : ℕ, if A has a bounded-bias depth-three AMC proof of size s at shift ε (has_depth_three_amc_bounded_bias_proof n A ε s), then A has an arbitrary-bias depth-three AMC proof of size s at shift ε (has_depth_three_amc_proof n A ε s).
-/

/-- Every bounded-bias depth-three AMC proof is an arbitrary-bias depth-three AMC proof of the same size and shift. -/
theorem depth_three_amc_of_bounded_bias (n : ℕ) (A : List (List (CnfLit (Fin n)))) (ε : ℝ) (s : ℕ)
    (h : has_depth_three_amc_bounded_bias_proof n A ε s) :
    has_depth_three_amc_proof n A ε s := by
  obtain ⟨R, hR, hsum⟩ := h
  refine ⟨R, ?_, hsum⟩
  intro j
  obtain ⟨g, hg0, -, hg⟩ := hR j
  exact ⟨g, hg0, hg⟩
