import AFTD.Prelude
import AFTD.Kb.Tcs.IsMoorePenroseInverse

/-!
# is_resistance_regular

Topic: graphs   Node: 5bfa1fa7d688

Provenance: formalization of a published result. Source: arXiv:2611.21670 Definition 2.3 and Theorem 2.4

A finite simple graph G is resistance-regular if G is connected and there exists a Moore-Penrose pseudoinverse of its real Laplacian matrix whose diagonal entries are all equal.
-/

/-- A finite simple graph is resistance-regular if it is connected and the Moore-Penrose pseudoinverse of its Laplacian has constant diagonal. -/
def is_resistance_regular {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Prop :=
  G.Connected ∧
  ∃ L_pinv : Matrix V V ℝ,
    is_moore_penrose_inverse (G.lapMatrix ℝ) L_pinv ∧
    ∃ c : ℝ, ∀ v : V, L_pinv v v = c
