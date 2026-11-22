import AFTD.Prelude

/-!
# complete_coloring_quantum_sync_value_diff

Topic: quantum   Node: 83d9606428ac

Provenance: helper lemma. arXiv:2611.19002 Theorem 4.6.1 -- Quantum Coloring Games on Complete Graphs

For all natural numbers $n$ and $m$, and all real numbers $p$, $q$, and $r$, the difference $(p + (1 - p)(1 - \frac{n - m}{m(n - 1)})) - (p + (1 - p)(1 - \frac{(q - 1)n + (q + 1)r}{n(n - 1)}))$ equals $(1 - p)(\frac{(q - 1)n + (q + 1)r}{n(n - 1)} - \frac{n - m}{m(n - 1)})$.
-/

/-- The difference between the quantum and classical synchronous value expressions reduces to a difference of fractions multiplied by 1 - p. -/
theorem complete_coloring_quantum_sync_value_diff (n m : ℕ) (p : ℝ) (q r : ℝ) :
    (p + (1 - p) * (1 - ((n : ℝ) - (m : ℝ)) / ((m : ℝ) * ((n : ℝ) - 1)))) -
    (p + (1 - p) * (1 - ((q - 1) * (n : ℝ) + (q + 1) * r) / ((n : ℝ) * ((n : ℝ) - 1)))) =
      (1 - p) * (((q - 1) * (n : ℝ) + (q + 1) * r) / ((n : ℝ) * ((n : ℝ) - 1)) -
        ((n : ℝ) - (m : ℝ)) / ((m : ℝ) * ((n : ℝ) - 1))) := by
  ring
