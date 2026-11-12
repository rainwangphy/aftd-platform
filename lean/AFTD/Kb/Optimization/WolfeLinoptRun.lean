import AFTD.Prelude
import AFTD.Kb.Optimization.WolfeMajorCycle

/-!
# wolfe_linopt_run

Topic: submodular   Node: 2a74f0488873

Provenance: formalization of a published result. Source: arXiv:2611.12680 Sec. 2.2

For a set atoms : Set (Fin n → ℝ), a natural number k : ℕ, a family of subsets S : Fin (k + 1) → Finset (Fin n → ℝ), and vectors w : Fin (k + 1) → (Fin n → ℝ), wolfe_linopt_run atoms k S w asserts that for every i : Fin k, wolfe_major_cycle atoms (S i.castSucc) (S i.succ) (w i.castSucc) (w i.succ) holds, and for every q ∈ atoms, 0 ≤ ∑ i : Fin n, w (Fin.last k) i * (q i - w (Fin.last k) i).
-/

/-- A complete Wolfe run of length k under the linopt rule. -/
def wolfe_linopt_run {n : ℕ} (atoms : Set (Fin n → ℝ)) (k : ℕ)
    (S : Fin (k + 1) → Finset (Fin n → ℝ)) (w : Fin (k + 1) → (Fin n → ℝ)) : Prop :=
  (∀ i : Fin k, wolfe_major_cycle atoms (S i.castSucc) (S i.succ) (w i.castSucc) (w i.succ)) ∧
  (∀ q ∈ atoms, 0 ≤ ∑ i : Fin n, w (Fin.last k) i * (q i - w (Fin.last k) i))
