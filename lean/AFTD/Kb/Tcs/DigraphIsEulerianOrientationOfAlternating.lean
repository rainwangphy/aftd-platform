import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphIsAlternatingOrientation
import AFTD.Kb.Tcs.DigraphIsEulerianOrientation
import AFTD.Kb.Tcs.SimpleGraphIsRotationSystem
import AFTD.Kb.Tcs.IsGraphOrientation

/-!
# digraph_is_eulerian_orientation_of_alternating

Topic: graphs   Node: afdb1e2f53cc

Provenance: helper lemma. Sanity lemma for digraph_is_alternating_orientation (OP-541)

An alternating orientation (for any rotation system) is Eulerian: around each vertex σ maps outgoing darts bijectively to incoming ones (sanity check of digraph_is_alternating_orientation).
-/

theorem digraph_is_eulerian_orientation_of_alternating {n : ℕ} (G : SimpleGraph (Fin n))
    [DecidableRel G.Adj] (σ : Equiv.Perm G.Dart) (hσ : simple_graph_is_rotation_system G σ)
    (D : Digraph (Fin n)) [DecidableRel D.Adj] (hD : digraph_is_alternating_orientation G σ D) :
    digraph_is_eulerian_orientation G D := by
  classical
  unfold digraph_is_eulerian_orientation
  refine ⟨hD.1, fun v => ?_⟩
  show (Finset.univ.filter (fun w : Fin n => D.Adj v w)).card
      = (Finset.univ.filter (fun w : Fin n => D.Adj w v)).card
  set T : Finset (Fin n) := Finset.univ.filter (fun w => D.Adj v w) with hT
  set U : Finset (Fin n) := Finset.univ.filter (fun w => D.Adj w v) with hU
  set X : Finset G.Dart := Finset.univ.filter (fun d => d.fst = v ∧ D.Adj v d.snd) with hX
  set Y : Finset G.Dart := Finset.univ.filter (fun d => d.fst = v ∧ ¬ D.Adj v d.snd) with hY
  have htest : ∀ d : G.Dart, d ∈ X ↔ d.fst = v ∧ D.Adj v d.snd := by
    intro d; rw [hX]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have htestY : ∀ d : G.Dart, d ∈ Y ↔ d.fst = v ∧ ¬ D.Adj v d.snd := by
    intro d; rw [hY]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 : X.card = T.card := by
    apply Finset.card_bij (fun d (_ : d ∈ X) => d.snd)
    · intro d hd
      rw [htest] at hd; rw [hT]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]; exact hd.2
    · intro d1 hd1 d2 hd2 heq
      rw [htest] at hd1 hd2
      exact SimpleGraph.Dart.ext d1 d2 (Prod.ext (hd1.1.trans hd2.1.symm) heq)
    · intro w hw
      rw [hT] at hw; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨G.dartOfNeighborSet v ⟨w, (hD.1.1 v w).mp (Or.inl hw)⟩, ?_, ?_⟩
      · rw [htest]; exact ⟨rfl, by simpa [SimpleGraph.dartOfNeighborSet] using hw⟩
      · rfl
  have h2 : Y.card = U.card := by
    apply Finset.card_bij (fun d (_ : d ∈ Y) => d.snd)
    · intro d hd
      rw [htestY] at hd; rw [hU]; simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      have hG : G.Adj v d.snd := hd.1 ▸ d.adj
      rcases (hD.1.1 v d.snd).mpr hG with h | h
      · exact absurd h hd.2
      · exact h
    · intro d1 hd1 d2 hd2 heq
      rw [htestY] at hd1 hd2
      exact SimpleGraph.Dart.ext d1 d2 (Prod.ext (hd1.1.trans hd2.1.symm) heq)
    · intro w hw
      rw [hU] at hw; simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hw
      refine ⟨G.dartOfNeighborSet v ⟨w, (hD.1.1 v w).mp (Or.inr hw)⟩, ?_, ?_⟩
      · rw [htestY]; refine ⟨rfl, ?_⟩
        simp only [SimpleGraph.dartOfNeighborSet]
        exact fun h => hD.1.2 v w ⟨h, hw⟩
      · rfl
  have h3 : X.card = Y.card := by
    apply Finset.card_bij (fun d (_ : d ∈ X) => σ d)
    · intro d hd
      rw [htest] at hd; rw [htestY]; refine ⟨?_, ?_⟩
      · exact (hσ.1 d).trans hd.1
      · have h := (hD.2 d).mp (hd.1.symm ▸ hd.2)
        rw [hσ.1 d, hd.1] at h
        exact h
    · intro d1 hd1 d2 hd2 heq
      exact σ.injective heq
    · intro e he
      rw [htestY] at he
      refine ⟨σ.symm e, ?_, by simp⟩
      rw [htest]
      have hv : (σ.symm e).fst = v := by
        have h := hσ.1 (σ.symm e)
        simp only [Equiv.apply_symm_apply] at h
        exact h ▸ he.1
      refine ⟨hv, ?_⟩
      have h := (hD.2 (σ.symm e)).mpr
      simp only [Equiv.apply_symm_apply] at h
      rw [← hv]
      apply h
      exact he.1.symm ▸ he.2
  calc T.card = X.card := h1.symm
    _ = Y.card := h3
    _ = U.card := h2
