import AFTD.Prelude
import AFTD.Kb.Tcs.LcsLength

/-!
# insdel_dist

Topic: information   Node: 5909c84dd118

Provenance: formalization of a published result. Source: arXiv:2611.21275 Lemma 1

The insertion-deletion distance between two vectors $u, v \in \alpha^n$ is $2(n - l_{\mathrm{LCS}}(u, v))$.
-/

/-- The insertion-deletion (insdel) distance between two words of length n. -/
noncomputable def insdel_dist {n : ℕ} {α : Type*} (u v : Fin n → α) : ℕ := 2 * (n - lcs_length u v)
