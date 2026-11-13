import AFTD.Prelude
import AFTD.Kb.Tcs.DigitExchangeWalsh

/-!
# digit_exchange_walsh_prob

Topic: cryptography   Node: 5f602eeb0a77

Provenance: original. Related work: arXiv:2611.02572

Given a natural number m, c in GaloisField 2 m, and j in Nat, digit_exchange_walsh_prob m c j is the probability that the absolute value of digit_exchange_walsh m c u v s t equals j * 2^m, when the input mask (u,v) is chosen uniformly from (GaloisField 2 m)^2 and the output mask (s,t) is chosen uniformly from (GaloisField 2 m)^2 minus {(0,0)}.
-/

/-- Probability that |W(u,v;s,t)| = j * 2^m for random input masks and nonzero output masks. -/
noncomputable def digit_exchange_walsh_prob (m : ℕ) (c : GaloisField 2 m) (j : ℕ) : ℝ := by
  classical
  let F := GaloisField 2 m
  haveI : Fintype F := Fintype.ofFinite F
  let inputMasks : Finset (F × F) := Finset.univ
  let outputMasks : Finset (F × F) := Finset.univ.filter (· ≠ (0, 0))
  let totalMasks : Finset ((F × F) × (F × F)) := inputMasks ×ˢ outputMasks
  let favorable := totalMasks.filter (fun ⟨⟨u, v⟩, ⟨s, t⟩⟩ =>
    |digit_exchange_walsh m c u v s t| = (j : ℤ) * (2 : ℤ) ^ m)
  exact (favorable.card : ℝ) / (totalMasks.card : ℝ)
