import AFTD.Prelude
import AFTD.Kb.Tcs.PrmEvalMap

/-!
# prmCode

Topic: information   Node: 765525182070

Provenance: formalization of a published result. Source: arXiv:2611.08203 Section 2.1

Given a field K and natural numbers d and m, prmCode K d m is the projective Reed-Muller code PRM(d, m) over K, defined as the K-subspace of functions from Projectivization K (Fin (m + 1) → K) to K given by the range LinearMap.range (prmEvalMap K d m).
-/

/-- The projective Reed-Muller code PRM(d, m) over K. -/
noncomputable def prmCode (K : Type*) [Field K] (d m : ℕ) :
    Subspace K (Projectivization K (Fin (m + 1) → K) → K) := LinearMap.range (prmEvalMap K d m)
