import AFTD.Prelude
import AFTD.Kb.Tcs.HasCommonSubsequence

/-!
# lcs_length

Topic: information   Node: f0f4a557fad3

Provenance: formalization of a published result. Source: arXiv:2611.21275 Section II-B

The length of the longest common subsequence of two vectors $u, v \in \alpha^n$ is the supremum of lengths $l \le n$ for which $u$ and $v$ have a common subsequence of length $l$.
-/

/-- The length of the longest common subsequence (LCS) of two words of length n. -/
noncomputable def lcs_length {n : ℕ} {α : Type*} (u v : Fin n → α) : ℕ := sSup {l : ℕ | l ≤ n ∧ has_common_subsequence u v l}
