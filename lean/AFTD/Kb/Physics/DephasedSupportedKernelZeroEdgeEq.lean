import AFTD.Prelude
import AFTD.Kb.Physics.DephasedSupportedKernel
import AFTD.Kb.Physics.TreeSubmatrixKer

/-!
# dephased_supported_kernel_zero_edge_eq

Topic: quantum_mechanics   Node: ffee4e32f148

Provenance: helper lemma. Linear-algebra half of the zero-edge entropy reduction for OP-827; checked numerically in experiments 22383 and 22398.

Deleting an edge between two zero-parameter vertices does not change the cut-kernel subspace supported at nonzero-parameter vertices.
-/

theorem dephased_supported_kernel_zero_edge_eq {V : Type*} [Fintype V] [DecidableEq V] (G G' : SimpleGraph V) [DecidableRel G.Adj] [DecidableRel G'.Adj] (u v : V) (hedge : ∀ x y : V, G'.Adj x y ↔ G.Adj x y ∧ ¬ ((x = u ∧ y = v) ∨ (x = v ∧ y = u))) (q : V → ℝ) (hu : q u = 0) (hv : q v = 0) (S : Finset V) : dephased_supported_kernel G q S = dephased_supported_kernel G' q S := by
  classical
  ext x
  change (x ∈ tree_submatrix_ker G S ∧ (∀ i : ↥S, q i.1 = 0 → x i = 0)) ↔
    (x ∈ tree_submatrix_ker G' S ∧ (∀ i : ↥S, q i.1 = 0 → x i = 0))
  have hsame (hx : ∀ i : ↥S, q i.1 = 0 → x i = 0) :
      Matrix.toLin' ((G.adjMatrix (ZMod 2)).submatrix
        (fun (r : ↥(Sᶜ : Finset V)) => (r : V)) (fun (c : ↥S) => (c : V))) x =
      Matrix.toLin' ((G'.adjMatrix (ZMod 2)).submatrix
        (fun (r : ↥(Sᶜ : Finset V)) => (r : V)) (fun (c : ↥S) => (c : V))) x := by
    ext r
    simp only [Matrix.toLin'_apply, Matrix.mulVec, dotProduct, Matrix.submatrix_apply]
    apply Finset.sum_congr rfl
    intro c hc
    by_cases hz : q c.1 = 0
    · simp [hx c hz]
    · have hcu : c.1 ≠ u := by intro h; exact hz (h ▸ hu)
      have hcv : c.1 ≠ v := by intro h; exact hz (h ▸ hv)
      have hadj : G.Adj r.1 c.1 ↔ G'.Adj r.1 c.1 := by
        rw [hedge]
        simp [hcu, hcv]
      simp only [SimpleGraph.adjMatrix_apply]
      split_ifs <;> simp_all
  constructor
  · rintro ⟨h, hx⟩
    refine ⟨?_, hx⟩
    change Matrix.toLin' _ x = 0 at h ⊢
    rwa [← hsame hx]
  · rintro ⟨h, hx⟩
    refine ⟨?_, hx⟩
    change Matrix.toLin' _ x = 0 at h ⊢
    rwa [hsame hx]
