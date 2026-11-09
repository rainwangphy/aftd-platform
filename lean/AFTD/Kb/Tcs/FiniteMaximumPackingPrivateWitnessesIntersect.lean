import AFTD.Prelude
import AFTD.Kb.Tcs.FiniteMaximumPackingConflictsSatisfyHall

/-!
# finite_maximum_packing_private_witnesses_intersect

Topic: combinatorics   Node: aa8d9939a823

Provenance: helper lemma. Elementary maximum-packing exchange for the active-vertex reduction.

In a finite set family with nonempty members, if P is a maximum pairwise-disjoint packing and two family members each avoid every member of P except possibly p, then the two family members intersect.
-/

theorem finite_maximum_packing_private_witnesses_intersect
    {α : Type*} [DecidableEq α] (F P : Finset (Finset α))
    (hnonempty : ∀ t ∈ F, t.Nonempty)
    (hPF : P ⊆ F)
    (hPdis : (P : Set (Finset α)).Pairwise Disjoint)
    (hmax : ∀ Q : Finset (Finset α), Q ⊆ F →
      (Q : Set (Finset α)).Pairwise Disjoint → Q.card ≤ P.card)
    (p T U : Finset α) (hT : T ∈ F) (hU : U ∈ F)
    (hTprivate : ∀ q ∈ P, q ≠ p → Disjoint q T)
    (hUprivate : ∀ q ∈ P, q ≠ p → Disjoint q U) :
    ¬ Disjoint T U := by
  classical
  intro hTU
  have hne : T ≠ U := by
    intro h
    subst U
    exact (hnonempty T hT).ne_empty (disjoint_self.mp hTU)
  let W : Finset (Finset α) := {T,U}
  have hWF : W ⊆ F := by
    intro q hq
    simp only [W, Finset.mem_insert, Finset.mem_singleton] at hq
    rcases hq with rfl | rfl
    · exact hT
    · exact hU
  have hWdis : (W : Set (Finset α)).Pairwise Disjoint := by
    intro a ha b hb hab
    simp only [W, Finset.mem_coe, Finset.mem_insert, Finset.mem_singleton] at ha hb
    rcases ha with rfl | rfl <;> rcases hb with rfl | rfl
    · exact (hab rfl).elim
    · exact hTU
    · exact hTU.symm
    · exact (hab rfl).elim
  have hhall := finite_maximum_packing_conflicts_satisfy_hall F P W
    hnonempty hPF hWF hPdis hWdis hmax W (Finset.Subset.rfl)
  have hsub : P.filter (fun q => ¬ Disjoint q (W.biUnion id)) ⊆ {p} := by
    intro q hq
    by_contra hn
    have hqp : q ≠ p := by simpa using hn
    have hqP : q ∈ P := (Finset.mem_filter.mp hq).1
    have hdT := hTprivate q hqP hqp
    have hdU := hUprivate q hqP hqp
    have hd : Disjoint q (W.biUnion id) := by
      rw [Finset.disjoint_biUnion_right]
      intro s hs
      simp only [W, Finset.mem_insert, Finset.mem_singleton] at hs
      rcases hs with rfl | rfl
      · exact hdT
      · exact hdU
    exact (Finset.mem_filter.mp hq).2 hd
  have hcard := Finset.card_le_card hsub
  have hWcard : W.card = 2 := by simp [W, hne]
  rw [hWcard] at hhall
  simp only [Finset.card_singleton] at hcard
  omega
