import AFTD.Prelude
import AFTD.Kb.Optimization.IsSubmodularBounded
import AFTD.Kb.Optimization.IsEpsFarSubmodular
import AFTD.Kb.Optimization.HypercubeRelDist

/-!
# op_932_submodular_not_far

Topic: submodular   Node: f9e26da76c53

Provenance: helper lemma. arXiv:2611.02374 Def. 2.4

For any positive ε, a submodular function from Fin n → Bool to Fin (k + 1) is not ε-far from submodularity.
-/

/-- A submodular function is never ε-far from submodularity for any positive ε. -/
theorem op_932_submodular_not_far (n k : ℕ) (f : (Fin n → Bool) → Fin (k + 1))
    (hf : is_submodular_bounded n k f) (ε : ℝ) (hε : 0 < ε) :
    ¬ is_eps_far_submodular n k ε f := by
  intro h
  have hf_near := h f hf
  simp [hypercube_rel_dist] at hf_near
  linarith
