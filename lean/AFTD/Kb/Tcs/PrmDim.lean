import AFTD.Prelude
import AFTD.Kb.Tcs.PrmCode

/-!
# prmDim

Topic: information   Node: 1661b7b280da

Provenance: formalization of a published result. Source: arXiv:2611.08203 Section 6.2

Given a field K and natural numbers d and m, prmDim K d m is the dimension Module.finrank K of the projective Reed-Muller code prmCode K d m.
-/

/-- The dimension k_d(m) of PRM(d, m). -/
noncomputable def prmDim (K : Type*) [Field K] (d m : ℕ) : ℕ := Module.finrank K (prmCode K d m)
