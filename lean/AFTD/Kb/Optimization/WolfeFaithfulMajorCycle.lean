import AFTD.Prelude
import AFTD.Kb.Optimization.IsWolfeCorral
import AFTD.Kb.Optimization.WolfeMinorStep

/-!
# wolfe_faithful_major_cycle

Topic: submodular   Node: a40efeb5a7ec

Provenance: formalization of a published result. Source: arXiv:2611.12680 Sec. 2.2 Algorithm 2

For a set atoms of vectors in ℝ^n, corrals S and S' with centers w and w', wolfe_faithful_major_cycle atoms S S' w w' asserts that S and S' are Wolfe corrals contained in atoms, and there exists an atom p_in ∈ atoms with ∑ i : Fin n, w i * (p_in i - w i) < 0 minimizing ∑ i, w i * q i over atoms, and strictly positive weights c on S summing to 1 with w = ∑ p ∈ S, c p • p, such that starting from T_init = insert p_in S with weights lam_init vanishing on p_in and equal to c on S, the reflexive-transitive closure of wolfe_minor_step reaches (S', lam_final) for some lam_final.
-/

/-- A major cycle under Wolfe's linopt rule, executing minor cycles from the inserted atom. -/
def wolfe_faithful_major_cycle {n : ℕ} (atoms : Set (Fin n → ℝ))
    (S S' : Finset (Fin n → ℝ)) (w w' : Fin n → ℝ) : Prop :=
  is_wolfe_corral S w ∧
  is_wolfe_corral S' w' ∧
  (∀ p ∈ S, p ∈ atoms) ∧
  (∀ p ∈ S', p ∈ atoms) ∧
  ∃ (p_in : Fin n → ℝ) (c : (Fin n → ℝ) → ℝ),
    p_in ∈ atoms ∧
    (∑ i : Fin n, w i * (p_in i - w i) < 0) ∧
    (∀ q ∈ atoms, ∑ i : Fin n, w i * p_in i ≤ ∑ i : Fin n, w i * q i) ∧
    (∑ p ∈ S, c p = 1) ∧ (∀ p ∈ S, 0 < c p) ∧ (∀ p ∉ S, c p = 0) ∧ (w = ∑ p ∈ S, c p • p) ∧
    let lam_init : (Fin n → ℝ) → ℝ := fun p => if p = p_in then 0 else c p
    let T_init : Finset (Fin n → ℝ) := insert p_in S
    ∃ lam_final : (Fin n → ℝ) → ℝ,
      Relation.ReflTransGen wolfe_minor_step (T_init, lam_init) (S', lam_final)
