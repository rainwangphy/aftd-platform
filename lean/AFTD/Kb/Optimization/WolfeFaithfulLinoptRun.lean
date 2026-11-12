import AFTD.Prelude
import AFTD.Kb.Optimization.WolfeFaithfulMajorCycle

/-!
# wolfe_faithful_linopt_run

Topic: submodular   Node: 51056afdc3ce

Provenance: formalization of a published result. Source: arXiv:2611.12680 Sec. 2.2

For atoms : Set (Fin n → ℝ), run length k : ℕ, corrals S : Fin (k + 1) → Finset (Fin n → ℝ), and centers w : Fin (k + 1) → (Fin n → ℝ), wolfe_faithful_linopt_run atoms k S w asserts that each step from S(i) to S(i.succ) is a faithful Wolfe major cycle, and for every atom q ∈ atoms, 0 ≤ ∑ i : Fin n, w (Fin.last k) i * (q i - w (Fin.last k) i).
-/

/-- A full execution of Wolfe's method with the linopt rule from an initial corral to optimality. -/
def wolfe_faithful_linopt_run {n : ℕ} (atoms : Set (Fin n → ℝ)) (k : ℕ)
    (S : Fin (k + 1) → Finset (Fin n → ℝ)) (w : Fin (k + 1) → (Fin n → ℝ)) : Prop :=
  (∀ i : Fin k, wolfe_faithful_major_cycle atoms (S i.castSucc) (S i.succ) (w i.castSucc) (w i.succ)) ∧
  (∀ q ∈ atoms, 0 ≤ ∑ i : Fin n, w (Fin.last k) i * (q i - w (Fin.last k) i))
