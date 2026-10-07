import AFTD.Prelude
import AFTD.Kb.Optimization.PermGroupSymmetrize
import AFTD.Kb.Optimization.FinsetIndicatorVec

/-!
# is_strongly_symmetric_instance

Topic: submodular   Node: 4948272aad61

Provenance: formalization of a published result. Source: arXiv:2610.07387 (Stronger hardness for submodular maximization subject to a matroid constraint), Definition 2.1 (strong symmetry)

The problem max{f(S) : S independent in M} is strongly symmetric with respect to a permutation group G: f(σ(S)) = f(S) for all S and σ ∈ G, and two sets with equal symmetrized indicator vectors E_σ[1_{σ(S)}] are both independent or both dependent.
-/

/-- The problem `max {f(S) : S independent in M}` is strongly symmetric with respect to the permutation group `G`: `f(σ(S)) = f(S)` for every `σ ∈ G`, and two sets with the same symmetrized indicator vector are both independent or both dependent. -/
def is_strongly_symmetric_instance {m : ℕ} (M : Matroid (Fin m)) (f : Finset (Fin m) → ℝ)
    (G : Subgroup (Equiv.Perm (Fin m))) : Prop :=
  (∀ σ ∈ G, ∀ S : Finset (Fin m), f (S.map σ.toEmbedding) = f S) ∧
    ∀ S S' : Finset (Fin m),
      perm_group_symmetrize G (finset_indicator_vec S) =
        perm_group_symmetrize G (finset_indicator_vec S') →
      (M.Indep ↑S ↔ M.Indep ↑S')
