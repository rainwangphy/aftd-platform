import AFTD.Prelude
import AFTD.Kb.Tcs.IsKExtendable
import AFTD.Kb.Tcs.ExtendibleTwoOddAnticompleteShoresComplementUnmatchable
import AFTD.Kb.Tcs.PerfectMatchingOfAdjacencyInvolution
import AFTD.Kb.Tcs.InducedOddComponentsLeIndependence
import AFTD.Kb.Tcs.FiniteSubsetHasMaximumMatching
import AFTD.Kb.Tcs.MaximumMatchingSizeFromIndependence
import AFTD.Kb.Tcs.M
import AFTD.Kb.Tcs.C

/-!
# op1957_dense_balanced_half_conditions_do_not_force_separator

Topic: graphs   Node: b730b8ec3daf

Provenance: helper lemma. OP-1957: clique-join control for the separator-transfer route; experiment 42155.

There is a graph on 16 vertices of minimum degree at least 10 and independence number at most two, whose every induced subgraph has at most two odd components and whose every eight-vertex induced subgraph has a matching of at least three edges, yet which has a seven-vertex separator and is not 4-extendible.
-/

private def separatorControl : SimpleGraph (Fin 16) where
  Adj u v := u ≠ v ∧ ¬ ((u.val < 4 ∧ 4 ≤ v.val ∧ v.val < 9) ∨
                         (v.val < 4 ∧ 4 ≤ u.val ∧ u.val < 9))
  symm := ⟨by
    intro u v h
    exact ⟨h.1.symm, by simpa [or_comm] using h.2⟩⟩
  loopless := ⟨by intro v h; exact h.1 rfl⟩

local instance  aftdLocal_f875dc8b2a91628b_0 : DecidableRel separatorControl.Adj := by
  unfold separatorControl
  infer_instance

private def P : Finset (Fin 16) := {1,2,3}
private def Q : Finset (Fin 16) := {4,5,6,7,8}
private def Wfin : Finset (Fin 16) := {0,9,10,11,12,13,14,15}
private def W : Set (Fin 16) := {v | v ∈ Wfin}
private def mate : Fin 16 → Fin 16 :=
  ![15,1,2,3,4,5,6,7,8,10,9,12,11,14,13,0]

set_option maxHeartbeats 4000000 in
theorem in1238_separator_control_not_extendible : ¬ is_k_extendable separatorControl 4 := by
  classical
  intro hext
  have hp : P.card % 2 = 1 := by decide
  have hq : Q.card % 2 = 1 := by decide
  have hd : Disjoint P Q := by decide
  have hcross : ∀ a ∈ P, ∀ b ∈ Q, ¬ separatorControl.Adj a b := by decide
  have heq : ({v : Fin 16 | v ∉ P ∧ v ∉ Q} : Set (Fin 16)) = W := by
    ext v
    fin_cases v <;> simp [P,Q,W,Wfin]
  have hw : ({v : Fin 16 | v ∉ P ∧ v ∉ Q} : Set (Fin 16)).ncard = 2*4 := by
    rw [heq]
    change (Wfin : Set (Fin 16)).ncard = 2*4
    rw [Set.ncard_coe_finset]
    decide
  have hn := extendible_two_odd_anticomplete_shores_complement_unmatchable separatorControl 4 hext P Q hp hq hd hcross hw
  rw [heq] at hn
  let f (v : W) : W := ⟨mate v.val, by
    rcases v with ⟨v,hv⟩
    change v ∈ Wfin at hv
    change mate v ∈ Wfin
    fin_cases v <;> simp [Wfin,mate] at hv ⊢⟩
  have hi : Function.Involutive f := by
    intro v
    apply Subtype.ext
    rcases v with ⟨v,hv⟩
    fin_cases v <;> simp [f,mate]
  have ha : ∀ v : W, (separatorControl.induce W).Adj v (f v) := by
    intro v
    rcases v with ⟨v,hv⟩
    change v ∈ Wfin at hv
    change separatorControl.Adj v (mate v)
    fin_cases v <;> simp [Wfin,separatorControl,mate] at hv ⊢
  exact hn (perfect_matching_of_adjacency_involution _ f hi ha)



set_option maxHeartbeats 4000000 in
theorem in1238_separator_control_properties :
    (∀ v : Fin 16, ∃ N : Finset (Fin 16), 10 ≤ N.card ∧ ∀ u ∈ N, separatorControl.Adj v u) ∧
    (∀ I : Finset (Fin 16),
      (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ separatorControl.Adj u v) → I.card ≤ 2) ∧
    (∀ C : Finset (Fin 16),
      (separatorControl.induce {v | v ∈ C}).oddComponents.ncard ≤ 2) ∧
    (∀ C : Finset (Fin 16), C.card = 8 →
      ∃ M : separatorControl.Subgraph, M.IsMatching ∧ M.verts ⊆ (C : Set (Fin 16)) ∧
        3 ≤ M.edgeSet.ncard) ∧
    (∃ X U V : Finset (Fin 16), X.card=7 ∧ U.Nonempty ∧ V.Nonempty ∧
      Disjoint X U ∧ Disjoint X V ∧ Disjoint U V ∧ X ∪ U ∪ V = Finset.univ ∧
      (∀ u ∈ U, ∀ v ∈ V, ¬ separatorControl.Adj u v)) ∧
    ¬ is_k_extendable separatorControl 4 := by
  classical
  have hdeg : ∀ v : Fin 16, 10 ≤ (separatorControl.neighborFinset v).card := by decide
  have htriangle : ∀ x y z : Fin 16, x ≠ y → x ≠ z → y ≠ z →
      separatorControl.Adj x y ∨ separatorControl.Adj x z ∨ separatorControl.Adj y z := by decide
  have hind : ∀ I : Finset (Fin 16),
      (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ separatorControl.Adj u v) → I.card ≤ 2 := by
    intro I hI
    by_contra h
    obtain ⟨a,ha,b,hb,c,hc,hab,hac,hbc⟩ := Finset.two_lt_card.mp (by omega : 2 < I.card)
    rcases htriangle a b c hab hac hbc with hab' | hac' | hbc'
    · exact hI a ha b hb hab hab'
    · exact hI a ha c hc hac hac'
    · exact hI b hb c hc hbc hbc'
  refine ⟨?_,hind,?_,?_,?_,in1238_separator_control_not_extendible⟩
  · intro v
    refine ⟨separatorControl.neighborFinset v,hdeg v,?_⟩
    intro u hu
    simpa using hu
  · intro C
    exact induced_odd_components_le_independence separatorControl {v | v ∈ C} 2 hind
  · intro C hC
    obtain ⟨M,hM,hMC,hmax⟩ := finite_subset_has_maximum_matching separatorControl C
    have hh := maximum_matching_size_from_independence separatorControl C M hM hMC hmax 2 hind
    exact ⟨M,hM,hMC,by omega⟩
  · refine ⟨{9,10,11,12,13,14,15},{0,1,2,3},{4,5,6,7,8},?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> decide

theorem op1957_dense_balanced_half_conditions_do_not_force_separator :
    ∃ G : SimpleGraph (Fin 16),
    (∀ v : Fin 16, ∃ N : Finset (Fin 16), 10 ≤ N.card ∧ ∀ u ∈ N, G.Adj v u) ∧
    (∀ I : Finset (Fin 16),
      (∀ u ∈ I, ∀ v ∈ I, u ≠ v → ¬ G.Adj u v) → I.card ≤ 2) ∧
    (∀ C : Finset (Fin 16),
      (G.induce {v | v ∈ C}).oddComponents.ncard ≤ 2) ∧
    (∀ C : Finset (Fin 16), C.card = 8 →
      ∃ M : G.Subgraph, M.IsMatching ∧ M.verts ⊆ (C : Set (Fin 16)) ∧
        3 ≤ M.edgeSet.ncard) ∧
    (∃ X U V : Finset (Fin 16), X.card=7 ∧ U.Nonempty ∧ V.Nonempty ∧
      Disjoint X U ∧ Disjoint X V ∧ Disjoint U V ∧ X ∪ U ∪ V = Finset.univ ∧
      (∀ u ∈ U, ∀ v ∈ V, ¬ G.Adj u v)) ∧
    ¬ is_k_extendable G 4 := by
  exact ⟨separatorControl, in1238_separator_control_properties⟩
