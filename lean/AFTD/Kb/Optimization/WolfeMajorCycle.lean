import AFTD.Prelude
import AFTD.Kb.Optimization.IsWolfeCorral

/-!
# wolfe_major_cycle

Topic: submodular   Node: ff249495f63a

Provenance: formalization of a published result. Source: arXiv:2611.12680 Sec. 2.2

For a set atoms : Set (Fin n → ℝ), finite subsets S, S' : Finset (Fin n → ℝ), and vectors w, w' : Fin n → ℝ, wolfe_major_cycle atoms S S' w w' asserts that (S, w) and (S', w') are Wolfe corrals with S ⊆ atoms and S' ⊆ atoms, and there exists p_in ∈ atoms such that ∑ i : Fin n, w i * (p_in i - w i) < 0, for all q ∈ atoms, ∑ i : Fin n, w i * p_in i ≤ ∑ i : Fin n, w i * q i, S' ⊆ insert p_in S, p_in ∈ S', and ∑ i : Fin n, w' i * w' i < ∑ i : Fin n, w i * w i.
-/

/-- A major cycle transition under the linopt rule in Wolfe's method. -/
def wolfe_major_cycle {n : ℕ} (atoms : Set (Fin n → ℝ))
    (S S' : Finset (Fin n → ℝ)) (w w' : Fin n → ℝ) : Prop :=
  is_wolfe_corral S w ∧
  is_wolfe_corral S' w' ∧
  (∀ p ∈ S, p ∈ atoms) ∧
  (∀ p ∈ S', p ∈ atoms) ∧
  ∃ p_in : Fin n → ℝ,
    p_in ∈ atoms ∧ (∑ i : Fin n, w i * (p_in i - w i) < 0) ∧
    (∀ q ∈ atoms, ∑ i : Fin n, w i * p_in i ≤ ∑ i : Fin n, w i * q i) ∧
    S' ⊆ insert p_in S ∧
    p_in ∈ S' ∧
    (∑ i : Fin n, w' i * w' i < ∑ i : Fin n, w i * w i)
