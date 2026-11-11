import AFTD.Prelude
import AFTD.Kb.Tcs.SplitGraphVarBound

/-!
# split_graph_max_var

Topic: graphs   Node: cd35373284ef

Provenance: formalization of a published result. Source: arXiv:2609.14826: Section 4

For a natural number n, split_graph_max_var n is the supremum over all natural numbers k in Finset.Ico 1 n of split_graph_var_bound n k.
-/

/-- Maximum variance among complete split graphs on n vertices. -/
noncomputable def split_graph_max_var (n : ℕ) : ℝ := ⨆ k ∈ Finset.Ico 1 n, split_graph_var_bound n k
