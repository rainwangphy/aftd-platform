import AFTD.Prelude
import AFTD.Kb.Tcs.IsKstCode

/-!
# is_kst_code_singleton

Topic: combinatorics   Node: ad21f6b1eaf5

Provenance: helper lemma. arXiv:2610.35136, Sharp Bounds for Graph-Codes Avoiding Complete Bipartite Differences, Section 1

Any singleton set consisting of a single graph on vertex set [n] is a K_{s,t}-code.
-/

/-- Any singleton family of graphs is a K_{s,t}-code. -/
theorem is_kst_code_singleton (s t n : ℕ) (G : SimpleGraph (Fin n)) : is_kst_code s t n {G} := by
  intro G₁ G₂ h₁ h₂ hne
  rw [Set.mem_singleton_iff] at h₁ h₂
  exact absurd (h₁.trans h₂.symm) hne
