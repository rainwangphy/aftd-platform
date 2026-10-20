import AFTD.Prelude
import AFTD.Kb.Tcs.GraphHasNoIndepSix

/-!
# card_edgeFinset_ge_55_of_no_indep_six

Topic: combinatorics   Node: e4ad199309e9

Provenance: formalization of a published result. Source: scout/2610-24484-erd-h-o-s-gy-arf-as-balanced-five-colorings.md:1291

If a simple graph on 26 vertices has no independent set of size 6, then it has at least 55 edges.
-/

/-- Any graph on 26 vertices with no independent set of size 6 has at least 55 edges. -/
theorem card_edgeFinset_ge_55_of_no_indep_six
    {V : Type*} [Fintype V] [DecidableEq V] (hcard : Fintype.card V = 26)
    (G : SimpleGraph V) [DecidableRel G.Adj] (hA : graph_has_no_indep_six G) :
    55 ≤ G.edgeFinset.card := by
  open Finset in
  have hcf : Gᶜ.CliqueFree 6 := by
    intro t ht
    rw [SimpleGraph.isNClique_iff] at ht
    obtain ⟨hcl, hcard6⟩ := ht
    obtain ⟨v, hv, w, hw, hadj⟩ := hA t hcard6
    have hne : v ≠ w := hadj.ne
    have hcompl : Gᶜ.Adj v w := hcl hv hw hne
    rw [SimpleGraph.compl_adj] at hcompl
    exact hcompl.2 hadj
  have hbound : (Gᶜ).edgeFinset.card ≤ 270 := by
    have h := SimpleGraph.CliqueFree.card_edgeFinset_le (G := Gᶜ) (r := 5) hcf
    simp [hcard] at h
    exact h
  have hcompl_edge : (Gᶜ).edgeFinset = (⊤ : SimpleGraph V).edgeFinset \ G.edgeFinset := by
    ext e
    induction e using Sym2.ind with
    | _ v w =>
      simp [SimpleGraph.mem_edgeFinset, SimpleGraph.mem_edgeSet, SimpleGraph.compl_adj]
  have hsum : (Gᶜ).edgeFinset.card + G.edgeFinset.card = 325 := by
    rw [hcompl_edge]
    rw [Finset.card_sdiff_add_card_eq_card
      (SimpleGraph.edgeFinset_subset_edgeFinset.2 le_top)]
    rw [SimpleGraph.card_edgeFinset_top_eq_card_choose_two, hcard]
    norm_num [Nat.choose_two_right]
  omega
