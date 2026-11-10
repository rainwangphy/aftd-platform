import AFTD.Prelude
import AFTD.Kb.Tcs.SimpleGraphSupportMaxPackingOutsideSwapPrivate
import AFTD.Kb.Tcs.SimpleGraphExternalK4PrivatePairDecreasesPacking
import AFTD.Kb.Tcs.SimpleGraphTrianglePackingNumber

/-!
# simple_graph_support_max_packing_external_k4_decreases_packing

Topic: graphs   Node: 720777b7cfde

Provenance: helper lemma. Support-maximal reduction of the fully forced K4 branch of the triangle-packing campaign; no novelty claim.

If a maximum triangle packing has maximum vertex support, a packed face abc and an outside fourth vertex x spanning a four-clique force deletion of ab and cx to decrease the packing number.
-/

open scoped Sym2
set_option maxRecDepth 10000
set_option maxHeartbeats 3000000

theorem simple_graph_support_max_packing_external_k4_decreases_packing (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj] (P : Finset (Finset (Fin n))) (htri : ∀ t ∈ P, G.IsNClique 3 t) (hdisj : (P : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1)) (hsupport : ∀ Q : Finset (Finset (Fin n)), (∀ t ∈ Q, G.IsNClique 3 t) → (Q : Set (Finset (Fin n))).Pairwise (fun t u => (t ∩ u).card ≤ 1) → Q.card = P.card → (Q.biUnion id).card ≤ (P.biUnion id).card) (hmax : P.card = simple_graph_triangle_packing_number G) (a b c x : Fin n) (hp : ({a,b,c} : Finset (Fin n)) ∈ P) (hx : x ∉ P.biUnion id) (hk4 : G.IsNClique 4 ({a,b,c,x} : Finset (Fin n))) : simple_graph_triangle_packing_number (G.deleteEdges {s(a,b),s(c,x)}) < simple_graph_triangle_packing_number G := by
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
  have hface1 : G.IsNClique 3 ({b,c,x} : Finset (Fin n)) := by
    refine ⟨SimpleGraph.IsClique.subset ?_ hk4.isClique, ?_⟩
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      aesop
    · simp [hbc,hbx,hcx,Ne.symm hbc,Ne.symm hbx,Ne.symm hcx]
  have hface2 : G.IsNClique 3 ({a,c,x} : Finset (Fin n)) := by
    refine ⟨SimpleGraph.IsClique.subset ?_ hk4.isClique, ?_⟩
    · intro v hv
      simp only [Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at hv ⊢
      aesop
    · simp [hac,hax,hcx,Ne.symm hac,Ne.symm hax,Ne.symm hcx]
  have heq1 : ({b,c,a} : Finset (Fin n)) = {a,b,c} := by ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have heq2 : ({a,c,b} : Finset (Fin n)) = {a,b,c} := by ext v; simp only [Finset.mem_insert, Finset.mem_singleton]; tauto
  have hp1 : ({b,c,a} : Finset (Fin n)) ∈ P := by rwa [heq1]
  have hp2 : ({a,c,b} : Finset (Fin n)) ∈ P := by rwa [heq2]
  have ha := simple_graph_support_max_packing_outside_swap_private n G P htri hdisj hsupport b c a x hp1 hx hface1
  have hb := simple_graph_support_max_packing_outside_swap_private n G P htri hdisj hsupport a c b x hp2 hx hface2
  have hprivate : ∀ q ∈ P, q ≠ ({a,b,c} : Finset (Fin n)) → a ∉ q ∧ b ∉ q := by
    intro q hq hne
    constructor
    · apply ha q hq
      rwa [heq1]
    · apply hb q hq
      rwa [heq2]
  exact simple_graph_external_k4_private_pair_decreases_packing n G P a b c x htri hdisj hmax hp hx hprivate hk4
