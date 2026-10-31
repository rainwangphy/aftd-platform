import AFTD.Prelude
import AFTD.Kb.Tcs.Graph11
import AFTD.Kb.Tcs.Graph11Diam
import AFTD.Kb.Tcs.GraphIsMutualVisibilityColorable
import AFTD.Kb.Tcs.GraphIsMutualVisibilitySet
import AFTD.Kb.Tcs.Support

/-!
# graph_11_not_is_mutual_visibility_colorable_two

Topic: graphs   Node: 620374f72715

Provenance: helper lemma. arXiv:2610.39430 Theorem 3.4

The simple graph G_11 is not mutual-visibility 2-colorable.
-/

set_option maxRecDepth 200000
set_option maxHeartbeats 1000000

open SimpleGraph

instance : DecidableRel graph_11.Adj := graph_11_diam_decidableAdj

lemma graph_11_not_is_mutual_visibility_colorable_two_walk_length_two
    {V : Type*} {G : SimpleGraph V} {u v : V} (p : G.Walk u v) (h : p.length = 2) :
    ∃ w, G.Adj u w ∧ G.Adj w v ∧ p.support = [u, w, v] := by
  cases p with
  | nil => contradiction
  | cons h1 p =>
    cases p with
    | nil => revert h; simp
    | cons h2 p =>
      cases p with
      | nil =>
        refine ⟨_, h1, h2, rfl⟩
      | cons _ _ => revert h; simp

lemma graph_11_not_is_mutual_visibility_colorable_two_dist_eq_two
    {u v : Fin 11} (hne : u ≠ v) (hnadj : ¬ graph_11.Adj u v) :
    graph_11.dist u v = 2 := by
  have hed : graph_11.edist u v ≤ 2 := graph_11_diam_edist_le_two u v
  have hr : graph_11.Reachable u v := by
    rw [← SimpleGraph.edist_ne_top_iff_reachable]
    intro htop
    rw [htop] at hed
    contradiction
  have hlt : 1 < graph_11.dist u v := SimpleGraph.Reachable.one_lt_dist_of_ne_of_not_adj hr hne hnadj
  have hle : graph_11.dist u v ≤ 2 := by
    rw [SimpleGraph.dist]
    exact ENat.toNat_le_of_le_natCast hed
  omega

lemma graph_11_not_is_mutual_visibility_colorable_two_mvs_nonadj
    {S : Set (Fin 11)} (hS : graph_is_mutual_visibility_set graph_11 S)
    {u v : Fin 11} (hu : u ∈ S) (hv : v ∈ S) (hne : u ≠ v) (hnadj : ¬ graph_11.Adj u v) :
    ∃ w : Fin 11, graph_11.Adj u w ∧ graph_11.Adj w v ∧ w ∉ S := by
  have hd : graph_11.dist u v = 2 := graph_11_not_is_mutual_visibility_colorable_two_dist_eq_two hne hnadj
  rcases hS u hu v hv with ⟨p, hp_len, hp_vis⟩
  rw [hd] at hp_len
  obtain ⟨w, huw, hwv, hsupp⟩ := graph_11_not_is_mutual_visibility_colorable_two_walk_length_two p hp_len
  refine ⟨w, huw, hwv, ?_⟩
  intro hwS
  have hw_supp : w ∈ p.support := by
    rw [hsupp]
    simp
  have hw_eq := hp_vis w hw_supp hwS
  rcases hw_eq with rfl | rfl
  · exact graph_11.ne_of_adj huw rfl
  · exact graph_11.ne_of_adj hwv rfl

def graph_11_not_is_mutual_visibility_colorable_two_bad (c : Fin 11 → Fin 2) : Prop :=
  ∃ u : Fin 11, ∃ v : Fin 11, c u = c v ∧ u ≠ v ∧ ¬ graph_11.Adj u v ∧
    ∀ w : Fin 11, graph_11.Adj u w → graph_11.Adj w v → c w = c u

instance (c : Fin 11 → Fin 2) : Decidable (graph_11_not_is_mutual_visibility_colorable_two_bad c) := by
  dsimp [graph_11_not_is_mutual_visibility_colorable_two_bad]
  infer_instance

instance : Decidable (∀ c : Fin 11 → Fin 2, graph_11_not_is_mutual_visibility_colorable_two_bad c) :=
  Fintype.decidableForallFintype

theorem graph_11_not_is_mutual_visibility_colorable_two_all_bad :
    ∀ c : Fin 11 → Fin 2, graph_11_not_is_mutual_visibility_colorable_two_bad c := by
  decide

/-- G_11 is not mutual-visibility 2-colorable. -/
theorem graph_11_not_is_mutual_visibility_colorable_two :
    ¬ graph_is_mutual_visibility_colorable graph_11 2 := by
  intro ⟨c, hc⟩
  obtain ⟨u, v, heq, hne, hnadj, hall⟩ := graph_11_not_is_mutual_visibility_colorable_two_all_bad c
  have hu : u ∈ {x | c x = c u} := rfl
  have hv : v ∈ {x | c x = c u} := heq.symm
  have hS : graph_is_mutual_visibility_set graph_11 {x | c x = c u} := hc (c u)
  obtain ⟨w, huw, hwv, hwnot⟩ := graph_11_not_is_mutual_visibility_colorable_two_mvs_nonadj hS hu hv hne hnadj
  have hcw : c w = c u := hall w huw hwv
  exact hwnot hcw
