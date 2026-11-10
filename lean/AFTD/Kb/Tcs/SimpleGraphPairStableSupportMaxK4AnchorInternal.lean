import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphSupportMaxPackingExternalK4DecreasesPacking
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_pair_stable_support_max_k4_anchor_internal

Topic: graphs   Node: d148b4c1c858

Provenance: helper lemma. Internal-anchor reduction for the general fully forced triangle-packing residual; no novelty claim.

In a two-edge-stable graph, every fourth vertex completing a packed triangle of a support-maximal maximum triangle packing to a four-clique already belongs to the packing vertex support.
-/

open scoped Sym2
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem simple_graph_pair_stable_support_max_k4_anchor_internal (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hsupport : ∀ Q : Finset (Finset (Fin n)), (∀ t ∈ Q, G.IsNClique 3 t) → (Q : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1) → Q.card = P.card → (Q.biUnion id).card ≤ (P.biUnion id).card) (hmax : P.card = simple_graph_triangle_packing_number G) (hstable : ∀ e f : Sym2 (Fin n), e ∈ G.edgeSet → f ∈ G.edgeSet → e ≠ f → simple_graph_triangle_packing_number (G.deleteEdges {e,f}) = simple_graph_triangle_packing_number G) (a b c x : Fin n) (hp : ({a,b,c} : Finset (Fin n)) ∈ P) (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n))) : x ∈ P.biUnion id := by
  classical
  have hab : a ≠ b := by
    intro h
    have hs : ({a,b,c,x} : Finset (Fin n)) ⊆ {a,c,x} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      clear * - h hv
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := c) (c := x)
    have h4 := hk4.card_eq
    omega
  have hac : a ≠ c := by
    intro h
    have hs : ({a,b,c,x} : Finset (Fin n)) ⊆ {a,b,x} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      clear * - h hv
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := x)
    have h4 := hk4.card_eq
    omega
  have hax : a ≠ x := by
    intro h
    have hs : ({a,b,c,x} : Finset (Fin n)) ⊆ {a,b,c} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      clear * - h hv
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := c)
    have h4 := hk4.card_eq
    omega
  have hbc : b ≠ c := by
    intro h
    have hs : ({a,b,c,x} : Finset (Fin n)) ⊆ {a,b,x} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      clear * - h hv
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := x)
    have h4 := hk4.card_eq
    omega
  have hbx : b ≠ x := by
    intro h
    have hs : ({a,b,c,x} : Finset (Fin n)) ⊆ {a,b,c} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      clear * - h hv
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := c)
    have h4 := hk4.card_eq
    omega
  have hcx : c ≠ x := by
    intro h
    have hs : ({a,b,c,x} : Finset (Fin n)) ⊆ {a,b,c} := by
      intro v hv
      simp only [Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      clear * - h hv
      aesop
    have hc := Finset.card_le_card hs
    have hb := Finset.card_le_three (a := a) (b := b) (c := c)
    have h4 := hk4.card_eq
    omega
  by_contra hx
  have he : s(a,b) ∈ G.edgeSet := by
    have ha : a ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
    have hb : b ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
    exact hk4.isClique ha hb hab
  have hf : s(c,x) ∈ G.edgeSet := by
    have hc : c ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
    have hx' : x ∈ ({a,b,c,x} : Finset (Fin n)) := by simp
    exact hk4.isClique hc hx' hcx
  have hef : s(a,b) ≠ s(c,x) := by simp [Sym2.eq_iff,hac,hax,hbc,hbx]
  have hd := simple_graph_support_max_packing_external_k4_decreases_packing n G P htri hdisj hsupport hmax a b c x hp hx hk4
  have hs := hstable s(a,b) s(c,x) he hf hef
  omega
