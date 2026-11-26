import AFTD.Prelude
import AFTD.Kb.Tcs.SaturatedBarrierPoolCommonNonneighborStrictDeficitBound
import AFTD.Kb.Tcs.IsKExtendable

/-!
# saturated_small_shore_singleton_pool_empty

Topic: graphs   Node: 1ded7cf88b80

Provenance: helper lemma. Positive-separator transfer for OP-1957; https://arxiv.org/abs/2611.22690.

Under the displayed saturated four-shore hypotheses, a singleton pool with a=1 and at most two exceptional groups is empty.
-/

theorem saturated_small_shore_singleton_pool_empty
    {I : Type*} [DecidableEq I]
    (k e : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hext : is_k_extendable G k)
    (hdegree : ∀ v, 2*k+1 ≤ (G.neighborFinset v).card)
    (hind : ∀ I : Finset (Fin (4*k)),
      (∀ x ∈ I, ∀ y ∈ I, x ≠ y → ¬ G.Adj x y) → I.card ≤ k)
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card)
    (A B E : Finset (Fin (4*k))) (F : Fin 4 → Finset (Fin (4*k)))
    (J : Finset I) (Q : I → Finset (Fin (4*k)))
    (hA : A.card=5) (hAB : Disjoint A B) (hEB : E ⊆ B)
    (hnoAB : ∀ a ∈ A, ∀ b ∈ B, ¬ G.Adj a b)
    (hFdis : ∀ i j, i ≠ j → Disjoint (F i) (F j))
    (hFzero : ∀ i : Fin 4, i ≠ 0 → Disjoint (F i) A)
    (hFE : ∀ i, Disjoint (F i) E)
    (hFanti : ∀ i, ∀ u ∈ F i, ∀ v ∈ E, ¬ G.Adj u v)
    (hQsub : ∀ i ∈ J, Q i ⊆ E) (hQne : ∀ i ∈ J, (Q i).Nonempty)
    (hQdis : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → Disjoint (Q i) (Q j))
    (hQanti : ∀ i ∈ J, ∀ j ∈ J, i ≠ j → ∀ u ∈ Q i, ∀ v ∈ Q j, ¬ G.Adj u v)
    (htotal : (∑ i : Fin 4, (F i).card) + E.card + J.card + e = 2*k)
    (hm : J.card ≤ k)
    (hsingle : E.card = J.card) (ha : (F 0 ∩ A).card = 1) (he : e ≤ 2) :
    J.card = 0 := by
  set_option maxHeartbeats 4000000 in
    classical
    by_contra hn
    have hJ : J.Nonempty := Finset.card_pos.mp (Nat.pos_of_ne_zero hn)
    have hb := saturated_barrier_pool_common_nonneighbor_strict_deficit_bound k e G hext hdegree hind hsep
      A B E F J Q hA hAB hEB hnoAB hFdis hFzero hFE hFanti hQsub hQne hQdis hQanti htotal hm hJ
    omega
