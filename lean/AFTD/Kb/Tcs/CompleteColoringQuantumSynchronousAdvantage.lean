import AFTD.Prelude
import AFTD.Kb.Tcs.CompleteColoringQuantumSyncValueDiff
import AFTD.Kb.Tcs.CompleteColoringQuantumSyncFractionDiff

/-!
# complete_coloring_quantum_synchronous_advantage

Topic: quantum   Node: 71f3c3c102f2

Provenance: formalization of a published result. Source: arXiv:2611.19002 Theorem 4.6.1 -- Quantum Coloring Games on Complete Graphs

In the complete-graph coloring game on $K_n$ with $m$ colors and equal input probability $p$, for any natural numbers $n$ and $m$ satisfying $2 \le m < n$ and any real number $p$, letting $q = \lfloor n/m \rfloor$ and $r = n \bmod m$, the quantum synchronous advantage—the difference between the quantum synchronous value $p + (1-p)(1 - \frac{n-m}{m(n-1)})$ and the classical synchronous value $p + (1-p)(1 - \frac{(q-1)n+(q+1)r}{n(n-1)})$—equals $(1-p) \frac{r(m-r)}{mn(n-1)}$.
-/

/-- Theorem 4.6.1: Exact quantum synchronous advantage in complete-graph coloring games equals (1-p) * (r(m-r) / (mn(n-1))). -/
theorem complete_coloring_quantum_synchronous_advantage (n m : ℕ) (hnm : m < n) (hm : 2 ≤ m) (p : ℝ) :
    let q : ℝ := (n / m : ℕ)
    let r : ℝ := (n % m : ℕ)
    (p + (1 - p) * (1 - ((n : ℝ) - (m : ℝ)) / ((m : ℝ) * ((n : ℝ) - 1)))) -
    (p + (1 - p) * (1 - ((q - 1) * (n : ℝ) + (q + 1) * r) / ((n : ℝ) * ((n : ℝ) - 1)))) =
      (1 - p) * (r * ((m : ℝ) - r) / ((m : ℝ) * (n : ℝ) * ((n : ℝ) - 1))) := by
  intro q r
  rw [complete_coloring_quantum_sync_value_diff n m p q r]
  have hn : (n : ℝ) ≠ 0 := by
    have : 0 < n := by omega
    positivity
  have hm0 : (m : ℝ) ≠ 0 := by
    have : 0 < m := by omega
    positivity
  have hn1 : (n : ℝ) - 1 ≠ 0 := by
    have : (1 : ℝ) < (n : ℝ) := by
      exact_mod_cast (by omega : 1 < n)
    linarith
  have hdiv : (n : ℝ) = q * (m : ℝ) + r := by
    dsimp [q, r]
    have h_nat : n = (n / m) * m + n % m := by
      rw [Nat.mul_comm, Nat.div_add_mod]
    exact_mod_cast h_nat
  rw [complete_coloring_quantum_sync_fraction_diff (n : ℝ) (m : ℝ) q r hn hn1 hm0 hdiv]
