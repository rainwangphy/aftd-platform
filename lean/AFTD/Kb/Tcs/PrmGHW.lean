import AFTD.Prelude
import AFTD.Kb.Tcs.PrmCode
import AFTD.Kb.Tcs.GeneralizedHammingWeight

/-!
# prmGHW

Topic: information   Node: 4689b08fc7cf

Provenance: formalization of a published result. Source: arXiv:2611.08203 Section 2.1 & Remark 6.11

Given a finite field K with [Field K] [Fintype K] and natural numbers d, m, and r, prmGHW K d m r is the r-th generalized Hamming weight generalizedHammingWeight (prmCode K d m) r of the projective Reed-Muller code prmCode K d m on the finite projective space Projectivization K (Fin (m + 1) → K).
-/

/-- The r-th generalized Hamming weight of PRM(d, m). -/
noncomputable def prmGHW (K : Type*) [Field K] [Fintype K] (d m r : ℕ) : ℕ := letI : Fintype (Projectivization K (Fin (m + 1) → K)) := Fintype.ofFinite _
  generalizedHammingWeight (prmCode K d m) r
