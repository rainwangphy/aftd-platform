import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteColoringQuantumSyncNumeratorIdentity

/-!
# complete_coloring_quantum_sync_fraction_diff

Topic: quantum   Node: 19887e11a8da

Provenance: helper lemma. arXiv:2611.19002 Theorem 4.6.1 -- Quantum Coloring Games on Complete Graphs

For all real numbers $n$, $m$, $q$, and $r$ with $n \ne 0$, $n - 1 \ne 0$, $m \ne 0$, and $n = qm + r$, the difference of fractions $\frac{(q - 1)n + (q + 1)r}{n(n - 1)} - \frac{n - m}{m(n - 1)}$ equals $\frac{r(m - r)}{mn(n - 1)}$.
-/

/-- The difference of fractions over common denominator mn(n-1) reduces to r(m-r)/(mn(n-1)) when n = qm + r. -/
theorem complete_coloring_quantum_sync_fraction_diff (n m q r : ℝ) (hn : n ≠ 0) (hn1 : n - 1 ≠ 0) (hm : m ≠ 0) (hdiv : n = q * m + r) :
    ((q - 1) * n + (q + 1) * r) / (n * (n - 1)) - (n - m) / (m * (n - 1)) =
      (r * (m - r)) / (m * n * (n - 1)) := by
  have hnum := complete_coloring_quantum_sync_numerator_identity n m q r hdiv
  field_simp
  linarith [hnum]
