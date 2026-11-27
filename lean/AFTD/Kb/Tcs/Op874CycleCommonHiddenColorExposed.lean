import AFTD.Prelude
import AFTD.Kb.Tcs.Op874PermutationDisjointCover

/-!
# op874_cycle_common_hidden_color_exposed

Topic: graphs   Node: 067368b65be2

Provenance: helper lemma. Cycle-interface counting for OP-874, based on the local-state criterion in arXiv:2610.41950.

Let σ be a permutation of a finite set of vertices, and suppose each vertex has a unique marked one of three ports, numbered outside, forward, and backward. At every successor interface, the marked ports do not lie in both exposed pairs {outside,backward} and {outside,forward}. Then the marked port at every vertex is forward or backward, so it is exposed outside.
-/

theorem op874_cycle_common_hidden_color_exposed
    {V : Type*} [Fintype V] [DecidableEq V] (σ : V ≃ V)
    (p : V → Fin 3 → Prop)
    (hsome : ∀ v, p v 0 ∨ p v 1 ∨ p v 2)
    (hunique : ∀ v i j, i ≠ j → ¬ (p v i ∧ p v j))
    (hcross : ∀ v, ¬ (p v 0 ∧ p (σ v) 0) ∧
      ¬ (p v 0 ∧ p (σ v) 1) ∧ ¬ (p v 2 ∧ p (σ v) 0) ∧
      ¬ (p v 2 ∧ p (σ v) 1)) :
    ∀ v, ¬ p v 0 := by
  classical
  let A := Finset.univ.filter fun v => p v 1
  let B := Finset.univ.filter fun v => p v 2
  have hdis : Disjoint A B := by
    apply Finset.disjoint_left.mpr
    intro v ha hb
    exact hunique v 1 2 (by decide) ⟨(Finset.mem_filter.mp ha).2, (Finset.mem_filter.mp hb).2⟩
  have hcov : ∀ v, v ∈ A ∨ σ v ∈ B := by
    intro v
    simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and]
    have h1 := hsome v
    have h2 := hsome (σ v)
    have hc := hcross v
    tauto
  have hall := op874_permutation_disjoint_cover σ A B hdis hcov
  intro v hv
  have hd := hall v
  simp only [A, B, Finset.mem_filter, Finset.mem_univ, true_and] at hd
  rcases hd with h1 | h2
  · exact hunique v 0 1 (by decide) ⟨hv, h1⟩
  · exact hunique v 0 2 (by decide) ⟨hv, h2⟩
