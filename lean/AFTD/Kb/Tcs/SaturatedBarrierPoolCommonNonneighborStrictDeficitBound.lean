import AFTD.Prelude
import AFTD.Kb.Tcs.ExtendibleIndependentCommonNonneighborDeficitLeOne
import AFTD.Kb.Tcs.IsKExtendable

/-!
# saturated_barrier_pool_common_nonneighbor_strict_deficit_bound

Topic: graphs   Node: af366ac6c4f2

Provenance: helper lemma. Positive-separator transfer for OP-1957; https://arxiv.org/abs/2611.22690.

For the stated saturated four-shore data with a nonempty pool, the strict deficit bound forces m+4≤e+|E|+|F₀∩A|.
-/

private theorem in1214_pool_strict_of_common_nonneighbor_bound
    {I : Type*} [DecidableEq I]
    (k e : ℕ) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
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
    (hJ : J.Nonempty)
    (hstrict : ∀ U W : Finset (Fin (4*k)), Disjoint U W → U.Nonempty →
      (∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v) →
      (∀ u ∈ U, ∀ w ∈ W, ¬ G.Adj u w) → 2*U.card+W.card ≤ 2*k+1) :
    J.card+4 ≤ e+E.card+(F 0 ∩ A).card := by
  set_option maxHeartbeats 4000000 in
    classical
    let p : J → Fin (4*k) := fun i => (hQne i.val i.property).choose
    have hp : ∀ i : J, p i ∈ Q i.val := fun i => (hQne i.val i.property).choose_spec
    have hpinj : Function.Injective p := by
      intro i j hij
      apply Subtype.ext
      by_contra hne
      have hi := hp i
      have hj : p i ∈ Q j.val := by simpa [hij] using hp j
      exact Finset.disjoint_left.mp (hQdis i.val i.property j.val j.property hne) hi hj
    let U : Finset (Fin (4*k)) := Finset.univ.image p
    have hUcard : U.card=J.card := by
      dsimp [U]
      rw [Finset.card_image_of_injective _ hpinj]
      simp
    have hUne : U.Nonempty := by
      obtain ⟨i,hi⟩ := hJ
      refine ⟨p ⟨i,hi⟩,?_⟩
      exact Finset.mem_image.mpr ⟨⟨i,hi⟩,Finset.mem_univ _,rfl⟩
    have hUE : U ⊆ E := by
      intro x hx
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hx
      exact hQsub i.val i.property (hp i)
    have hUind : ∀ u ∈ U, ∀ v ∈ U, ¬ G.Adj u v := by
      intro u hu v hv huv
      obtain ⟨i,_,rfl⟩ := Finset.mem_image.mp hu
      obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hv
      by_cases hij : i.val=j.val
      · have hsub : i=j := Subtype.ext hij
        subst j
        exact (G.ne_of_adj huv) rfl
      · exact hQanti i.val i.property j.val j.property hij (p i) (hp i) (p j) (hp j) huv
    let Vshore : Finset (Fin (4*k)) := Finset.univ.biUnion F
    let W : Finset (Fin (4*k)) := A ∪ Vshore
    have hpair : (↑(Finset.univ : Finset (Fin 4)) : Set (Fin 4)).PairwiseDisjoint F := by
      intro i hi j hj hij
      exact hFdis i j hij
    have hVcard : Vshore.card = ∑ i : Fin 4, (F i).card := by
      dsimp [Vshore]
      rw [Finset.card_biUnion hpair]
    have hinter : A ∩ Vshore = A ∩ F 0 := by
      ext x
      constructor
      · intro hx
        have hxA := (Finset.mem_inter.mp hx).1
        have hxV := (Finset.mem_inter.mp hx).2
        obtain ⟨i,_,hxi⟩ := Finset.mem_biUnion.mp hxV
        by_cases hi : i=0
        · subst i
          exact Finset.mem_inter.mpr ⟨hxA,hxi⟩
        · exact False.elim (Finset.disjoint_left.mp (hFzero i hi) hxi hxA)
      · intro hx
        have hxA := (Finset.mem_inter.mp hx).1
        have hx0 := (Finset.mem_inter.mp hx).2
        exact Finset.mem_inter.mpr ⟨hxA,Finset.mem_biUnion.mpr ⟨0,Finset.mem_univ _,hx0⟩⟩
    have hWcard : W.card+(F 0 ∩ A).card = 5+∑ i : Fin 4, (F i).card := by
      have hh := Finset.card_union_add_card_inter A Vshore
      rw [hinter,Finset.inter_comm A (F 0),hA,hVcard] at hh
      exact hh
    have hUW : Disjoint U W := by
      apply Finset.disjoint_left.mpr
      intro x hxU hxW
      have hxE := hUE hxU
      rcases Finset.mem_union.mp hxW with hxA | hxV
      · exact Finset.disjoint_left.mp hAB hxA (hEB hxE)
      · obtain ⟨i,_,hxi⟩ := Finset.mem_biUnion.mp hxV
        exact Finset.disjoint_left.mp (hFE i) hxi hxE
    have hanti : ∀ u ∈ U, ∀ w ∈ W, ¬ G.Adj u w := by
      intro u hu w hw huw
      have huE := hUE hu
      rcases Finset.mem_union.mp hw with hwA | hwV
      · exact hnoAB w hwA u (hEB huE) huw.symm
      · obtain ⟨i,_,hwi⟩ := Finset.mem_biUnion.mp hwV
        exact hFanti i w hwi u huE huw.symm
    have hb := hstrict U W hUW hUne hUind hanti
    rw [hUcard] at hb
    omega

theorem saturated_barrier_pool_common_nonneighbor_strict_deficit_bound
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
    (hJ : J.Nonempty) :
    J.card+4 ≤ e+E.card+(F 0 ∩ A).card := by
  set_option maxHeartbeats 4000000 in
    classical
    exact in1214_pool_strict_of_common_nonneighbor_bound k e G A B E F J Q hA hAB hEB hnoAB
      hFdis hFzero hFE hFanti hQsub hQne hQdis hQanti htotal hJ
      (fun U W hdis hUn hUind hanti =>
        extendible_independent_common_nonneighbor_deficit_le_one k G hext hdegree hind U W hdis hUn hUind hanti)
