import AFTD.Prelude
import AFTD.Kb.Tcs.PathInterIndepSetCardLe

/-!
# path_inter_indep_set_not_subset_of_card_lt

Topic: graphs   Node: 65d0a920913b

Provenance: helper lemma. arXiv:2611.06362, Section 2.2, Claim 2.2

If a simple path in a simple graph has its vertices contained in W ∪ U, where W is an independent set and |U| + 1 < |W|, then the path cannot contain all vertices of W.
-/

/-- A simple path supported on W ∪ U cannot contain all of W if W is an independent set and |U| + 1 < |W|. -/
lemma path_inter_indep_set_not_subset_of_card_lt {V : Type*} [DecidableEq V] {G : SimpleGraph V}
    {u v : V} (p : G.Walk u v) (hp : p.IsPath) (W U : Finset V)
    (hW : G.IsIndepSet (W : Set V))
    (hsub : p.support.toFinset ⊆ W ∪ U)
    (hcard : U.card + 1 < W.card) :
    ¬ (W ⊆ p.support.toFinset) := by
  intro hWsub
  have h1 := path_inter_indep_set_card_le p hp W hW
  have h2 : p.support.toFinset ∩ W = W := Finset.inter_eq_right.mpr hWsub
  have h3 : p.support.toFinset \ W ⊆ U := by
    intro x hx
    simp only [Finset.mem_sdiff] at hx
    have hx_union := hsub hx.1
    simp only [Finset.mem_union] at hx_union
    rcases hx_union with hxW | hxU
    · exact (hx.2 hxW).elim
    · exact hxU
  have h4 : (p.support.toFinset \ W).card ≤ U.card := Finset.card_le_card h3
  rw [h2] at h1
  omega
