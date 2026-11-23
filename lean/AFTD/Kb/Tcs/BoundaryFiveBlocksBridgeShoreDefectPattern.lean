import AFTD.Prelude
import AFTD.Kb.Tcs.BoundaryFiveBlocksBridgeShoreDefectConstraints
import AFTD.Kb.Tcs.BoundaryFiveBlocksStrongShoreSeparatorBound
import AFTD.Kb.Tcs.BoundaryFiveBlocksShortCShoreArithmetic
import AFTD.Kb.Tcs.BoundaryFiveBlocksTwoDefectShoreArithmetic

/-!
# boundary_five_blocks_bridge_shore_defect_pattern

Topic: graphs   Node: e0461fca3789

Provenance: helper lemma. OP-1957: assembly of the nonclique bridge-shore count and separator.

Under the displayed four-block, minimum-degree and separator hypotheses, the indicated even bridge shores have at least two A vertices on the x side if x has at most one opposite-block nonneighbor. If x has exactly two such nonneighbors, both lie on the y side and the x side has no A vertices and exactly one B vertex. No clique or matching hypothesis is assumed.
-/

theorem boundary_five_blocks_bridge_shore_defect_pattern
    (k : ℕ) (hk : 5 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (A B C D : Finset (Fin (4*k)))
    (hAB : Disjoint A B) (hAC : Disjoint A C) (hAD : Disjoint A D)
    (hBC : Disjoint B C) (hBD : Disjoint B D) (hCD : Disjoint C D)
    (hcover : A ∪ B ∪ C ∪ D = Finset.univ)
    (hA : A.card=5) (hC : C.card=5)
    (hsizeAB : A.card+B.card=2*k) (hsizeCD : C.card+D.card=2*k)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hnoCD : ∀ c ∈ C, ∀ d ∈ D, ¬ G.Adj c d)
    (hdegree : ∀ v, 2*k+2 ≤ (G.neighborFinset v).card)
    (hsep : ∀ X U V : Finset (Fin (4*k)), U.Nonempty → V.Nonempty →
      Disjoint X U → Disjoint X V → Disjoint U V → X ∪ U ∪ V = Finset.univ →
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v) → 2*k ≤ X.card)
    (x y : Fin (4*k)) (hx : x ∈ A) (hy : y ∈ C)
    (Q W : Finset (Fin (4*k))) (hQW : Disjoint Q W)
    (hxQ : x ∉ Q) (hyQ : y ∉ Q) (hxW : x ∉ W) (hyW : y ∉ W)
    (hQeven : Even Q.card) (hWeven : Even W.card)
    (hsize : (Q ∪ W ∪ {x,y}).card = 2*k)
    (hyQadj : ∀ q ∈ Q, ¬ G.Adj y q)
    (hxWadj : ∀ w ∈ W, ¬ G.Adj x w)
    (hcross : ∀ q ∈ Q, ∀ w ∈ W, ¬ G.Adj q w)
    : let r := (C.filter (fun c => ¬ G.Adj x c)).card;
      (r ≤ 1 → 2 ≤ (Q ∩ A).card) ∧
      (r = 2 → (W ∩ C).card = 2 ∧ (Q ∩ A).card = 0 ∧ (Q ∩ B).card = 1) := by  classical
  dsimp only
  have hc := boundary_five_blocks_bridge_shore_defect_constraints k hk G A B C D
    hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoAB hnoCD hdegree
    x y hx hy Q W hQW hxQ hyQ hxW hyW hQeven hWeven hsize hyQadj hxWadj hcross
  dsimp only at hc
  rcases hc with ⟨hm,hr,hrc,hcapA,hcapB,hcapC,hcapD,hQ,hW,hQe,hWe,htotal,
    hrootx,hrooty,hqa,hqb,hqc,hqd,hwa,hwb,hwc,hwd⟩
  have hs : 0 < (Q ∩ D).card →
      (Q ∩ D).card + (W ∩ B).card + (W ∩ D).card ≤ 2*k-5 := by
    intro hp
    have hne : (D ∩ Q).Nonempty := by
      apply Finset.card_pos.mp
      simpa [Finset.inter_comm] using hp
    have hh := boundary_five_blocks_strong_shore_separator_bound k hk G A B C D
      hAB hAC hAD hBC hBD hCD hcover hA hC hsizeAB hsizeCD hnoCD hsep Q W hQW hcross hne
    simpa only [Finset.inter_comm] using hh
  constructor
  · intro hr1
    apply boundary_five_blocks_short_c_shore_arithmetic (2*k-5)
      (C.filter (fun c => ¬ G.Adj x c)).card (Q∩A).card (Q∩B).card (Q∩C).card (Q∩D).card
      (W∩A).card (W∩B).card (W∩C).card (W∩D).card Q.card W.card
      hm hr hrc hcapA hcapB hcapC hcapD hQ hW hQe hWe htotal hrootx hrooty
      hqa hqb hqc hqd hwa hwb hwc hwd hs
    omega
  · intro hr2
    exact boundary_five_blocks_two_defect_shore_arithmetic (2*k-5)
      (C.filter (fun c => ¬ G.Adj x c)).card (Q∩A).card (Q∩B).card (Q∩C).card (Q∩D).card
      (W∩A).card (W∩B).card (W∩C).card (W∩D).card Q.card W.card
      hm hr2 hrc hcapA hcapB hcapC hcapD hQ hW hQe hWe htotal hrootx hrooty
      hqa hqb hqc hqd hwa hwb hwc hwd hs
