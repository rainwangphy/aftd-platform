import AFTD.Prelude
import AFTD.Kb.Tcs.CyclicMatrixFourier

/-!
# cyclic_matrix_fourier_zero_zero_ne_zero

Topic: combinatorics   Node: 8922d89c65f2

Provenance: helper lemma. step towards sharp_cyclic_graph_is_regular

For any finite graph G with at least one edge and any bijection π : ZMod N ≃ V, the (0,0) entry of the cyclic 2D Fourier transform of the adjacency matrix is nonzero.
-/

/-- If G has at least one edge, the (0,0) entry of its cyclic Fourier transform under any bijection π is nonzero, because it is (1/N) times the positive sum of non-negative adjacency indicators. -/
theorem cyclic_matrix_fourier_zero_zero_ne_zero {V : Type*} [Fintype V] (N : ℕ) [NeZero N]
    (G : SimpleGraph V) [DecidableRel G.Adj] (π : ZMod N ≃ V) (he : ∃ u v, G.Adj u v) :
    cyclic_matrix_fourier N (Matrix.of fun x y => if G.Adj (π x) (π y) then (1 : ℂ) else 0) 0 0 ≠ 0 := by
  unfold cyclic_matrix_fourier
  simp
  refine ⟨NeZero.ne N, ?_⟩
  intro h
  rw [← Nat.cast_sum, Nat.cast_eq_zero] at h
  rcases he with ⟨u, v, huv⟩
  have hpos_card : 0 < (Finset.filter (fun y => G.Adj (π (π.symm u)) (π y)) Finset.univ).card := by
    rw [Finset.card_pos]
    refine ⟨π.symm v, ?_⟩
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    simpa using huv
  have hle := Finset.single_le_sum (f := fun x => (Finset.filter (fun y => G.Adj (π x) (π y)) Finset.univ).card)
    (fun _ _ => Nat.zero_le _) (Finset.mem_univ (π.symm u))
  omega
