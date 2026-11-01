import AFTD.Prelude
import AFTD.Kb.Tcs.LinearOrderMin

/-!
# lift_linear_order_min_eq

Topic: quantum   Node: ebdf3c56a8f8

Provenance: helper lemma. arXiv:2610.34762 Lemma 6 proof (Step 5)

If the global minimum of a linear order on Fin n lies in the range of an embedding f from Fin k to Fin n with f(j) = m, then j is the unique minimum of the induced linear order on Fin k.
-/

/-- The pre-image of the global minimum under an embedding is the minimum of the induced linear order. -/
theorem lift_linear_order_min_eq {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (L : LinearOrder (Fin n)) (f : Fin k ↪ Fin n) (j : Fin k)
    (hj : f j = linearOrderMin hn L) :
    linearOrderMin hk (LinearOrder.lift' f.toFun f.injective) = j := by
  change @Finset.min' (Fin k) (LinearOrder.lift' f.toFun f.injective) Finset.univ _ = j
  rw [@Finset.min'_eq_iff (Fin k) (LinearOrder.lift' f.toFun f.injective) Finset.univ _ j]
  refine ⟨Finset.mem_univ _, ?_⟩
  intro b _
  show (LinearOrder.lift' f.toFun f.injective).le j b
  change L.le (f j) (f b)
  rw [hj]
  exact @Finset.min'_le (Fin n) L Finset.univ (f b) (Finset.mem_univ _)
