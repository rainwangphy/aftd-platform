import AFTD.Prelude
import AFTD.Kb.Tcs.GtGraph
import AFTD.Kb.Tcs.ConnectedForcingPoly
import AFTD.Kb.Tcs.ZeroForcingPoly
import AFTD.Kb.Tcs.GtVertex
import AFTD.Kb.Tcs.ZeroForced
import AFTD.Kb.Tcs.IsConnectedForcingSet
import AFTD.Kb.Tcs.IsZeroForcingSet
import AFTD.Kb.Tcs.GtAdj

/-!
# gt_connected_forcing_poly_eq

Topic: graphs   Node: 79d8c0a6d0d8

Provenance: helper lemma. arXiv:2611.11352 Corollary 2

For every integer t ≥ 24, the connected forcing polynomial of gt_graph t is equal to the zero forcing polynomial of gt_graph t.
-/

lemma gt_connected_forcing_poly_eq_exists_ne_fin (t : ℕ) (ht : 2 ≤ t) (i : Fin t) : ∃ k : Fin t, k ≠ i := by
  by_cases h : i = ⟨0, by omega⟩
  · use ⟨1, by omega⟩
    intro heq
    have : (⟨1, by omega⟩ : Fin t).val = i.val := congr_arg Fin.val heq
    subst h
    norm_num at this
  · use ⟨0, by omega⟩
    intro heq
    exact h heq.symm

lemma gt_connected_forcing_poly_eq_adj_R_of_not_R (t : ℕ) (u : GtVertex t) (h : ∀ j, u ≠ GtVertex.R j) (k : Fin t) :
    (gt_graph t).Adj u (GtVertex.R k) := by
  dsimp [gt_graph, SimpleGraph.fromRel]
  cases u with
  | A _ => simp [gt_adj]
  | B _ => simp [gt_adj]
  | C _ => simp [gt_adj]
  | D _ => simp [gt_adj]
  | P _ => simp [gt_adj]
  | Q _ => simp [gt_adj]
  | R j => exact False.elim (h j rfl)

lemma gt_connected_forcing_poly_eq_not_zeroForced_R {t : ℕ} (ht : 2 ≤ t) {S : Set (GtVertex t)}
    (hS : ∀ i : Fin t, GtVertex.R i ∉ S) :
    ∀ v, ZeroForced (gt_graph t) S v → ∀ i : Fin t, v ≠ GtVertex.R i := by
  intro v hv
  induction hv with
  | init u hu =>
    intro i heq
    subst heq
    exact hS i hu
  | step u w hu hadj hall ihu ihall =>
    intro i heq
    subst heq
    obtain ⟨k, hk⟩ := gt_connected_forcing_poly_eq_exists_ne_fin t ht i
    have hadj_k : (gt_graph t).Adj u (GtVertex.R k) := gt_connected_forcing_poly_eq_adj_R_of_not_R t u ihu k
    have hne_k : GtVertex.R k ≠ GtVertex.R i := by
      intro heq
      injection heq with heq'
      exact hk heq'
    exact ihall (GtVertex.R k) hadj_k hne_k k rfl

lemma gt_connected_forcing_poly_eq_adj_R (t : ℕ) (i : Fin t) (v : GtVertex t) (h : GtVertex.R i ≠ v) :
    (gt_graph t).Adj (GtVertex.R i) v := by
  dsimp [gt_graph, SimpleGraph.fromRel]
  cases v with
  | A _ => simp [gt_adj]
  | B _ => simp [gt_adj]
  | C _ => simp [gt_adj]
  | D _ => simp [gt_adj]
  | P _ => simp [gt_adj]
  | Q _ => simp [gt_adj]
  | R j =>
    simp only [gt_adj]
    have : i ≠ j := by
      intro heq
      subst heq
      exact h rfl
    tauto

lemma gt_connected_forcing_poly_eq_connected_induce_of_mem_R {t : ℕ} {S : Set (GtVertex t)}
    (i : Fin t) (hi : GtVertex.R i ∈ S) :
    ((gt_graph t).induce S).Connected := by
  rw [SimpleGraph.connected_iff_exists_forall_reachable]
  use ⟨GtVertex.R i, hi⟩
  rintro ⟨w, hw⟩
  by_cases h : GtVertex.R i = w
  · subst h
    exact SimpleGraph.Reachable.refl _
  · have hadj : (gt_graph t).Adj (GtVertex.R i) w := gt_connected_forcing_poly_eq_adj_R t i w h
    exact SimpleGraph.Adj.reachable hadj

lemma gt_connected_forcing_poly_eq_is_connected_forcing_set_iff_zero_forcing_set (t : ℕ) (ht : 24 ≤ t) (S : Set (GtVertex t)) :
    is_connected_forcing_set (gt_graph t) S ↔ is_zero_forcing_set (gt_graph t) S := by
  constructor
  · intro h
    exact h.1
  · intro h
    refine ⟨h, ?_⟩
    by_contra hc
    have h_no_R : ∀ i : Fin t, GtVertex.R i ∉ S := by
      intro i hi
      exact hc (gt_connected_forcing_poly_eq_connected_induce_of_mem_R i hi)
    have ht2 : 2 ≤ t := by omega
    have h_not := gt_connected_forcing_poly_eq_not_zeroForced_R ht2 h_no_R
    have h0 : (0 : ℕ) < t := by omega
    have h_forced := h (GtVertex.R ⟨0, h0⟩)
    exact h_not (GtVertex.R ⟨0, h0⟩) h_forced ⟨0, h0⟩ rfl

/-- Connected forcing polynomial of G_t equals its zero forcing polynomial. -/
theorem gt_connected_forcing_poly_eq (t : ℕ) (ht : 24 ≤ t) :
    connected_forcing_poly (gt_graph t) = zero_forcing_poly (gt_graph t) := by
  dsimp [connected_forcing_poly, zero_forcing_poly]
  apply Finset.sum_congr rfl
  intro S _
  rw [gt_connected_forcing_poly_eq_is_connected_forcing_set_iff_zero_forcing_set t ht]
