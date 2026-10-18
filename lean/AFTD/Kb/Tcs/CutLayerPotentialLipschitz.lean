import AFTD.Prelude
import AFTD.Kb.Tcs.CutLayerPotential

/-!
# cut_layer_potential_lipschitz

Topic: graphs   Node: 8ea0d3e44cf0

Provenance: helper lemma. step towards exists_dist_three_cut_potential_witness

The 4-layer potential satisfies f a - f b ≤ dist(a, b) for all vertices a, b.
-/

lemma cut_layer_potential_lipschitz_nonneg {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (v : V) :
    0 ≤ cut_layer_potential G X v := by
  unfold cut_layer_potential
  split_ifs <;> norm_num

lemma cut_layer_potential_lipschitz_le_three {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) (v : V) :
    cut_layer_potential G X v ≤ 3 := by
  unfold cut_layer_potential
  split_ifs <;> norm_num

lemma cut_layer_potential_lipschitz_of_mem {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) {v : V} (hv : v ∈ X) :
    cut_layer_potential G X v ≤ 1 := by
  unfold cut_layer_potential
  rw [if_pos hv]
  split_ifs <;> norm_num

lemma cut_layer_potential_lipschitz_of_not_mem {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) {v : V} (hv : v ∉ X) :
    2 ≤ cut_layer_potential G X v := by
  unfold cut_layer_potential
  rw [if_neg hv]
  split_ifs <;> norm_num

lemma cut_layer_potential_lipschitz_eq_two {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) {v : V}
    (hv : v ∉ X) (h : ∃ w ∈ X, G.Adj v w) :
    cut_layer_potential G X v = 2 := by
  unfold cut_layer_potential
  rw [if_neg hv, if_pos h]

lemma cut_layer_potential_lipschitz_eq_one {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) {v : V}
    (hv : v ∈ X) (h : ∃ w ∈ (Xᶜ : Finset V), G.Adj v w) :
    cut_layer_potential G X v = 1 := by
  unfold cut_layer_potential
  rw [if_pos hv, if_pos h]

lemma cut_layer_potential_lipschitz_adj {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) {u v : V} (h : G.Adj u v) :
    cut_layer_potential G X u - cut_layer_potential G X v ≤ 1 := by
  by_cases hu : u ∈ X
  · by_cases hv : v ∈ X
    · have := cut_layer_potential_lipschitz_of_mem G X hu
      have := cut_layer_potential_lipschitz_nonneg G X v
      linarith
    · have hfv := cut_layer_potential_lipschitz_eq_two G X hv ⟨u, hu, h.symm⟩
      have := cut_layer_potential_lipschitz_of_mem G X hu
      linarith
  · by_cases hv : v ∈ X
    · have hfu := cut_layer_potential_lipschitz_eq_two G X hu ⟨v, hv, h⟩
      have hfv := cut_layer_potential_lipschitz_eq_one G X hv ⟨u, Finset.mem_compl.mpr hu, h.symm⟩
      linarith
    · have := cut_layer_potential_lipschitz_le_three G X u
      have := cut_layer_potential_lipschitz_of_not_mem G X hv
      linarith

lemma cut_layer_potential_lipschitz_walk {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (X : Finset V) {u v : V} (p : G.Walk u v) :
    cut_layer_potential G X u - cut_layer_potential G X v ≤ (p.length : ℝ) := by
  induction p with
  | nil => simp
  | cons h q ih =>
    rw [SimpleGraph.Walk.length_cons]
    push_cast
    have h1 := cut_layer_potential_lipschitz_adj G X h
    linarith

/-- The 4-layer potential for any cut is 1-Lipschitz on any connected graph. -/
theorem cut_layer_potential_lipschitz
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (hG : G.Connected) (X : Finset V) (a b : V) :
    cut_layer_potential G X a - cut_layer_potential G X b ≤ (G.dist a b : ℝ) := by
  obtain ⟨p, hp⟩ := hG.exists_walk_length_eq_dist a b
  have h := cut_layer_potential_lipschitz_walk G X p
  rw [hp] at h
  exact h
