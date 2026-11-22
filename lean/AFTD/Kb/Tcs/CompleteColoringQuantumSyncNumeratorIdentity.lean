import AFTD.Prelude

/-!
# complete_coloring_quantum_sync_numerator_identity

Topic: quantum   Node: 0996e5bf65e3

Provenance: helper lemma. arXiv:2611.19002 Theorem 4.6.1 -- Quantum Coloring Games on Complete Graphs

For all real numbers $n$, $m$, $q$, and $r$ satisfying $n = qm + r$, the algebraic expression $m((q - 1)n + (q + 1)r) - n(n - m)$ equals $r(m - r)$.
-/

/-- Polynomial numerator identity simplifying the advantage difference when n = qm + r. -/
theorem complete_coloring_quantum_sync_numerator_identity (n m q r : ℝ) (hdiv : n = q * m + r) :
    m * ((q - 1) * n + (q + 1) * r) - n * (n - m) = r * (m - r) := by
  linear_combination -(n + r) * hdiv
