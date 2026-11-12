import AFTD.Prelude
import AFTD.Kb.Tcs.BpeLexRun

/-!
# bpe_density

Topic: algorithms   Node: 180a3c8c5dec

Provenance: original. Related work: knowledgebase

For natural numbers k and N and sequence w : Fin N → ℕ, the real token density bpe_density k N w is the length in ℝ of the list obtained by applying k greedy BPE merges to List.ofFn w, divided by N in ℝ.
-/

/-- The final token count divided by N as a real number, after k greedy BPE merges on w : Fin N → ℕ. -/
noncomputable def bpe_density (k : ℕ) (N : ℕ) (w : Fin N → ℕ) : ℝ := ((bpe_lex_run k (List.ofFn w)).length : ℝ) / (N : ℝ)
