import AFTD.Prelude
import AFTD.Kb.Tcs.IndexedDisjointCrossEdgesFormMatching

/-!
# balanced_cut_separator_implies_min_degree

Topic: graphs   Node: 82cb9c04a4cb

Provenance: helper lemma. Exposed-barrier reduction for OP-1957; https://arxiv.org/abs/2611.22690.

The displayed 2k-separator property forces minimum degree at least 2k.
-/

theorem balanced_cut_separator_implies_min_degree
    (k : ℕ) (hk : 1 ≤ k) (G : SimpleGraph (Fin (4*k))) [DecidableRel G.Adj]
    (hsep : ∀ S P Q : Finset (Fin (4*k)), P.Nonempty → Q.Nonempty →
      Disjoint S P → Disjoint S Q → Disjoint P Q → S ∪ P ∪ Q = Finset.univ →
      (∀ u ∈ P, ∀ v ∈ Q, ¬ G.Adj u v) → 2*k ≤ S.card) :
    ∀ v, 2*k ≤ (G.neighborFinset v).card := by
  set_option maxHeartbeats 4000000 in
    classical
    intro v
    by_contra hn
    let S := G.neighborFinset v
    let P : Finset (Fin (4*k)) := {v}
    let Q := Finset.univ \ (S ∪ P)
    have hP : P.Nonempty := by simp [P]
    have hSnot : v ∉ S := by simp [S]
    have hSlt : S.card < 2*k := by simpa [S] using (Nat.lt_of_not_ge hn)
    have hSP : Disjoint S P := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxP
      have hx : x=v := by simpa [P] using hxP
      exact hSnot (hx ▸ hxS)
    have hQ : Q.Nonempty := by
      apply Finset.card_pos.mp
      have hbound := Finset.card_union_le S P
      have hd := Finset.card_sdiff_add_card_inter (Finset.univ : Finset (Fin (4*k))) (S ∪ P)
      have hh : ((Finset.univ : Finset (Fin (4*k))) ∩ (S ∪ P)) = S ∪ P := by simp
      rw [hh] at hd
      simp only [Finset.card_univ,Fintype.card_fin] at hd
      have hp : P.card=1 := by simp [P]
      dsimp [Q]
      omega
    have hSQ : Disjoint S Q := by
      apply Finset.disjoint_left.mpr
      intro x hxS hxQ
      exact (Finset.mem_sdiff.mp hxQ).2 (Finset.mem_union_left P hxS)
    have hPQ : Disjoint P Q := by
      apply Finset.disjoint_left.mpr
      intro x hxP hxQ
      exact (Finset.mem_sdiff.mp hxQ).2 (Finset.mem_union_right S hxP)
    have hcover : S ∪ P ∪ Q = Finset.univ := by
      ext x
      simp [Q]
    have hanti : ∀ u ∈ P, ∀ w ∈ Q, ¬ G.Adj u w := by
      intro u hu w hw hadj
      have hu' : u=v := by simpa [P] using hu
      subst u
      have hwS : w ∈ S := by simpa [S] using hadj
      exact (Finset.mem_sdiff.mp hw).2 (Finset.mem_union_left P hwS)
    have hh := hsep S P Q hP hQ hSP hSQ hPQ hcover hanti
    exact hn hh
