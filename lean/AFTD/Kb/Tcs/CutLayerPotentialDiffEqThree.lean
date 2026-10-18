import AFTD.Prelude
import AFTD.Kb.Tcs.CutLayerPotential

/-!
# cut_layer_potential_diff_eq_three

Topic: graphs   Node: 8a5ac3306b95

Provenance: helper lemma. step towards exists_dist_three_cut_potential_witness

For any vertex x ∈ Xᶜ with no neighbours in X and y ∈ X with no neighbours in Xᶜ, cut_layer_potential G X x - cut_layer_potential G X y = 3.
-/

/-- The 4-layer potential evaluates to 3 on any interior vertex of Xᶜ and 0 on any interior vertex of X, giving difference 3. -/
theorem cut_layer_potential_diff_eq_three
    {V : Type} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj]
    (X : Finset V) (x y : V)
    (hx : x ∈ (Xᶜ : Finset V)) (hx_no : ∀ u ∈ X, ¬ G.Adj x u)
    (hy : y ∈ X) (hy_no : ∀ w ∈ (Xᶜ : Finset V), ¬ G.Adj y w) :
    cut_layer_potential G X x - cut_layer_potential G X y = 3 := by
  simp only [cut_layer_potential]
  have hxnot : x ∉ X := by simpa using hx
  rw [if_neg hxnot, if_pos hy]
  have hx_no' : ¬ ∃ u ∈ X, G.Adj x u := by
    rintro ⟨u, hu, hadj⟩; exact hx_no u hu hadj
  have hy_no' : ¬ ∃ w ∈ (Xᶜ : Finset V), G.Adj y w := by
    rintro ⟨w, hw, hadj⟩; exact hy_no w hw hadj
  rw [if_neg hx_no', if_neg hy_no']
  norm_num
