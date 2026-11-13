import AFTD.Prelude
import AFTD.Kb.Tcs.Op1525ThreeFixedPointsReconstruct
import AFTD.Kb.Tcs.SignedGraphIsBalancedPartition
import AFTD.Kb.Tcs.SignedGraphIsReconstructible
import AFTD.Kb.Tcs.SignedGraphReconstructibleBalancedMonoInvariant
import AFTD.Kb.Tcs.SignedGraphIsIsomorphic
import AFTD.Kb.Tcs.SignedGraphSwitch
import AFTD.Kb.Tcs.SignedGraphSameDeck
import AFTD.Kb.Tcs.SignedGraph
import AFTD.Kb.Tcs.G

/-!
# signed_graph_reconstructible_balanced_three_fixed

Topic: combinatorics   Node: e0b4d68334b1

Provenance: original. Related work: A structural subcase of OP-1525; compare arXiv:2611.13901, Section 4.1 and Remark 4.11.

Every connected balanced signed graph on at least seven vertices is reconstructible from its switching deck if its underlying graph has three distinct vertices fixed by every graph automorphism.
-/

namespace OP1525ThreePoly

lemma op1525_bool_xor_common (a b c : Bool) : xor (xor a c) (xor b c) = xor a b := by
  cases a <;> cases b <;> cases c <;> decide

lemma op1525_bool_xor_cancel_flip (a b c : Bool) :
    xor a true = xor (xor b true) c → a = xor b c := by
  cases a <;> cases b <;> cases c <;> decide

theorem op1525_three_fixed_points_reconstruct
    {V : Type*} [DecidableEq V] [Fintype V]
    (A B : V → Bool) (P : Equiv.Perm V → Prop)
    (r s t : V) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hsize : Fintype.card V ≥ 7)
    (hfix : ∀ g, P g → g r = r ∧ g s = s ∧ g t = t)
    (π : Equiv.Perm V)
    (hdeck : ∀ v, ∃ g, P g ∧ ∃ c : Bool, ∀ x,
      xor (A (g x)) (decide (g x = v)) =
        xor (xor (B x) (decide (x = π v))) c) :
    ∃ g, P g ∧ ∃ c : Bool, ∀ x, A (g x) = xor (B x) c := by
  classical
  let anchors : Finset V := {r, s, t}
  let bad : Finset V := anchors ∪ anchors.image π.symm
  have ha : anchors.card ≤ 3 := by
    dsimp [anchors]
    simp [hrs, hrt, hst]
  have hb : bad.card ≤ 6 := by
    have hu := Finset.card_union_le anchors (anchors.image π.symm)
    have hi := Finset.card_image_le (s := anchors) (f := π.symm)
    dsimp [bad]
    omega
  have hv : ∃ v, v ∉ bad := by
    by_contra h
    push_neg at h
    have he : bad = Finset.univ := by
      ext x
      simp [h x]
    have hc := congrArg Finset.card he
    simp only [Finset.card_univ] at hc
    omega
  obtain ⟨v, hv⟩ := hv
  have hvn : v ≠ r ∧ v ≠ s ∧ v ≠ t := by
    have h : v ∉ anchors := fun h => hv (Finset.mem_union_left _ h)
    simpa [anchors] using h
  have hvp : π v ≠ r ∧ π v ≠ s ∧ π v ≠ t := by
    have hnot : v ∉ anchors.image π.symm := by
      intro h
      exact hv (Finset.mem_union_right _ h)
    have hp : π v ∉ anchors := by
      intro h
      apply hnot
      exact Finset.mem_image.mpr ⟨π v, h, by simp⟩
    simpa [anchors] using hp
  obtain ⟨g, hg, c, hc⟩ := hdeck v
  obtain ⟨hgr, hgs, hgt⟩ := hfix g hg
  have er := hc r
  have es := hc s
  have et := hc t
  simp [hgr, hvn.1.symm, hvp.1.symm] at er
  simp [hgs, hvn.2.1.symm, hvp.2.1.symm] at es
  simp [hgt, hvn.2.2.symm, hvp.2.2.symm] at et
  have hbase1 : xor (A r) (A s) = xor (B r) (B s) := by
    rw [er, es]
    exact op1525_bool_xor_common _ _ _
  have hbase2 : xor (A r) (A t) = xor (B r) (B t) := by
    rw [er, et]
    exact op1525_bool_xor_common _ _ _
  obtain ⟨g', hg', c', hc'⟩ := hdeck r
  obtain ⟨hg'r, hg's, hg't⟩ := hfix g' hg'
  have e'r := hc' r
  have e's := hc' s
  have e't := hc' t
  have hπr : π r = r := by
    by_contra hn
    have hs : π r = s := by
      by_contra hs
      simp [hg'r, hg's, hrs.symm, Ne.symm hn, Ne.symm hs] at e'r e's
      cases hAr : A r <;> cases hAs : A s <;> cases hBr : B r <;>
        cases hBs : B s <;> cases hcc : c' <;>
          simp [hAr, hAs, hBr, hBs, hcc] at hbase1 e'r e's
    have ht : π r = t := by
      by_contra ht
      simp [hg'r, hg't, hrt.symm, Ne.symm hn, Ne.symm ht] at e'r e't
      cases hAr : A r <;> cases hAt : A t <;> cases hBr : B r <;>
        cases hBt : B t <;> cases hcc : c' <;>
          simp [hAr, hAt, hBr, hBt, hcc] at hbase2 e'r e't
    exact hst (hs.symm.trans ht)
  refine ⟨g', hg', c', ?_⟩
  intro x
  have heq := hc' x
  rw [hπr] at heq
  have he : (g' x = r) ↔ x = r := by
    constructor
    · intro h
      apply g'.injective
      simpa [hg'r] using h
    · intro h
      simpa [h] using hg'r
  by_cases hx : x = r
  · have hgx : g' x = r := he.mpr hx
    have h1 : decide (g' x = r) = true := by simp [hgx]
    have h2 : decide (x = r) = true := by simp [hx]
    rw [h1, h2] at heq
    exact op1525_bool_xor_cancel_flip _ _ _ heq
  · have hgx : g' x ≠ r := fun h => hx (he.mp h)
    simpa [hx, hgx] using heq

end OP1525ThreePoly

open OP1525Bridge

theorem signed_graph_reconstructible_balanced_three_fixed {V : Type*} [DecidableEq V] [Fintype V]
    (G : SignedGraph V) (hconn : G.graph.Connected) (hsize : Fintype.card V ≥ 7)
    (A B : Finset V) (hbal : G.IsBalancedPartition A B)
    (r s t : V) (hrs : r ≠ s) (hrt : r ≠ t) (hst : s ≠ t)
    (hfix : ∀ f : G.graph ≃g G.graph, f r = r ∧ f s = s ∧ f t = t) :
    G.IsReconstructible := by
  classical
  unfold SignedGraph.IsReconstructible
  intro W _ _ H hdeck
  obtain ⟨π0, hcards⟩ := hdeck
  obtain ⟨F, π, hcolors, hlift⟩ := OP1525Bridge.deck_color_model G H hconn A B hbal π0 hcards r
  let P : Equiv.Perm V → Prop := fun p => ∃ g : G.graph ≃g G.graph, g.toEquiv = p
  have hfixed : ∀ p, P p → p r = r ∧ p s = s ∧ p t = t := by
    intro p hp
    obtain ⟨g, rfl⟩ := hp
    exact hfix g
  have hmatch : ∀ w, ∃ g, P g ∧ ∃ d : Bool, ∀ x,
      xor (OP1525Bridge.color A (g x)) (decide (g x = w)) =
        xor (xor (F x) (decide (x = π w))) d := by
    intro w
    obtain ⟨g, d, hg⟩ := hcolors w
    refine ⟨g.toEquiv, ⟨g, rfl⟩, d, ?_⟩
    intro x
    simpa [OP1525Bridge.flipped] using hg x
  obtain ⟨p, ⟨g, rfl⟩, d, hd⟩ :=
    OP1525ThreePoly.op1525_three_fixed_points_reconstruct (OP1525Bridge.color A) F P
      r s t hrs hrt hst hsize hfixed π hmatch
  exact hlift g d hd
