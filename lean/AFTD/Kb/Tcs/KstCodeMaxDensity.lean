import AFTD.Prelude
import AFTD.Kb.Tcs.IsKstCode

/-!
# kst_code_max_density

Topic: combinatorics   Node: f0d21222969c

Provenance: formalization of a published result. Source: arXiv:2610.35136, Sharp Bounds for Graph-Codes Avoiding Complete Bipartite Differences, Section 1

The maximum density of a K_{s,t}-code in simple graphs on vertex set [n] is the supremum over all K_{s,t}-codes C of |C| / 2^{n choose 2}.
-/

/-- The maximum density of a K_{s,t}-code in simple graphs on Fin n. -/
noncomputable def kst_code_max_density (s t n : ℕ) : ℝ := open Classical in ⨆ (C : Set (SimpleGraph (Fin n))) (_hC : is_kst_code s t n C),
    (Set.ncard C : ℝ) / (2 ^ (n.choose 2) : ℝ)
