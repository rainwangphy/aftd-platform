import AFTD.Prelude
import AFTD.Kb.Tcs.HasDepthThreeAmcProof
import AFTD.Kb.Tcs.IsDnfTautology
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.IsRankOneProduct

/-!
# depth_three_amc_soundness

Topic: proof_complexity   Node: 199b339fe047

Provenance: formalization of a published result. Source: arXiv:2611.01055, Section 2.2, Proposition 2.2

For any natural number n, any DNF formula A : List (List (CnfLit (Fin n))), any real shift parameter ε > 0, and any proof size r : ℕ, if A has a depth-three AMC proof of size r at shift ε (has_depth_three_amc_proof n A ε r), then A is a DNF tautology (is_dnf_tautology A).
-/

/-- Soundness: if a DNF formula admits a depth-three AMC proof at positive shift, it is a tautology. -/
theorem depth_three_amc_soundness (n : ℕ) (A : List (List (CnfLit (Fin n)))) (ε : ℝ) (hε : 0 < ε) (r : ℕ)
    (h : has_depth_three_amc_proof n A ε r) : is_dnf_tautology A := by
  classical
  obtain ⟨R, hR, hsum⟩ := h
  unfold has_depth_three_amc_proof.match_1 at hsum
  intro τ
  by_contra hcon
  have hzero : (A.filter (fun t => decide (∀ l ∈ t,
      CnfLit.casesOn l (fun v => τ v = true) (fun v => τ v = false)))).length = 0 := by
    rw [List.length_eq_zero_iff, List.filter_eq_nil_iff]
    intro t ht
    simp only [decide_eq_true_eq]
    intro hh
    apply hcon
    refine ⟨t, ht, ?_⟩
    intro l hl
    have := hh l hl
    cases l <;> simpa using this
  have hnonneg : 0 ≤ ∑ j : Fin r, R j τ := by
    apply Finset.sum_nonneg
    intro j _
    obtain ⟨g, hg, hRg⟩ := hR j
    rw [hRg τ]
    exact Finset.prod_nonneg (fun i _ => hg i (τ i))
  have hh := hsum τ
  rw [hzero] at hh
  simp only [Nat.cast_zero] at hh
  linarith
