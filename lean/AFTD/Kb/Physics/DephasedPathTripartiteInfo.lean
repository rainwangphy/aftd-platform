import AFTD.Prelude
import AFTD.Kb.Physics.DephasedPathEntropy

/-!
# dephased_path_tripartite_info

Topic: quantum_mechanics   Node: 2630606caf07

Provenance: formalization of a published result. Source: arXiv:2511.19585, Monogamy of Mutual Information in Graph States

For n : ℕ, q : Fin n → ℝ, and finsets A, B, C : Finset (Fin n), the tripartite information dephased_path_tripartite_info n q A B C is dephased_path_entropy n q A + dephased_path_entropy n q B + dephased_path_entropy n q C - dephased_path_entropy n q (A ∪ B) - dephased_path_entropy n q (A ∪ C) - dephased_path_entropy n q (B ∪ C) + dephased_path_entropy n q (A ∪ B ∪ C).
-/

/-- Tripartite information I_3(A:B:C) defined by the dephased path entropy function. -/
noncomputable def dephased_path_tripartite_info (n : ℕ) (q : Fin n → ℝ) (A B C : Finset (Fin n)) : ℝ := dephased_path_entropy n q A + dephased_path_entropy n q B + dephased_path_entropy n q C -
  dephased_path_entropy n q (A ∪ B) - dephased_path_entropy n q (A ∪ C) - dephased_path_entropy n q (B ∪ C) +
  dephased_path_entropy n q (A ∪ B ∪ C)
