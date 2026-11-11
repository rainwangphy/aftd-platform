import AFTD.Prelude
import AFTD.Kb.Tcs.BipartiteSubsetStandardListColorable
import AFTD.Kb.Tcs.BipartiteSubsetGraph

/-!
# bipartite_subset_colorable_five_at_two

Topic: graphs   Node: f617ade0681e

Provenance: helper lemma. A finite base case for the two-color lifting route to OP-861, with explicit selector found in experiment 22164.

The standard lists color the bipartite subset graph at k = 5 and intersection threshold 2.
-/

def op861_five_near (i : Fin 9) : Finset (Fin 9) := {i+2, i+3, i+4, i+5}

set_option maxRecDepth 16384
set_option maxHeartbeats 2000000

theorem op861_five_cover : ∀ S : Finset (Fin 9), S.card = 5 →
    ∃ i ∈ S, 3 ≤ (S ∩ op861_five_near i).card := by
  decide


theorem op861_five_near_card (i : Fin 9) : (op861_five_near i).card = 4 := by
  fin_cases i <;> decide

theorem op861_five_not_near (i : Fin 9) : i ∉ op861_five_near i := by
  fin_cases i <;> decide

theorem op861_five_common (S T : Finset (Fin 9)) (i : Fin 9)
    (hiS : i ∈ S) (hiT : i ∈ T)
    (hS : 3 ≤ (S ∩ op861_five_near i).card)
    (hT : 3 ≤ (T ∩ op861_five_near i).card) :
    3 ≤ (S ∩ T).card := by
  let A := S ∩ op861_five_near i
  let B := T ∩ op861_five_near i
  have hsub : A ∪ B ⊆ op861_five_near i := by
    intro x hx
    simp only [Finset.mem_union, Finset.mem_inter, A, B] at hx
    tauto
  have hcard := Finset.card_le_card hsub
  rw [op861_five_near_card] at hcard
  have heq := Finset.card_union_add_card_inter A B
  have hAB : 2 ≤ (A ∩ B).card := by
    dsimp [A, B] at heq
    dsimp [A, B] at hcard
    dsimp [A, B]
    omega
  have hinot : i ∉ A ∩ B := by
    intro hi
    have hiQ : i ∈ op861_five_near i := (Finset.mem_inter.mp (Finset.mem_inter.mp hi).1).2
    exact op861_five_not_near i hiQ
  have hsub' : insert i (A ∩ B) ⊆ S ∩ T := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_inter] at hx ⊢
    rcases hx with rfl | ⟨hxA, hxB⟩
    · exact ⟨hiS, hiT⟩
    · exact ⟨(Finset.mem_inter.mp hxA).1, (Finset.mem_inter.mp hxB).1⟩
  have hbound := Finset.card_le_card hsub'
  rw [Finset.card_insert_of_notMem hinot] at hbound
  omega

noncomputable def op861_five_pick (S : {S : Finset (Fin 9) // S.card = 5}) : Fin 9 :=
  Classical.choose (op861_five_cover S.1 S.2)

theorem op861_five_pick_spec (S : {S : Finset (Fin 9) // S.card = 5}) :
    op861_five_pick S ∈ S.1 ∧
      3 ≤ (S.1 ∩ op861_five_near (op861_five_pick S)).card :=
  Classical.choose_spec (op861_five_cover S.1 S.2)

theorem bipartite_subset_colorable_five_at_two : bipartite_subset_standard_list_colorable 5 2 := by
  let col : ({S : Finset (Fin 9) // S.card = 5} ⊕
      {T : Finset (Fin 9) // T.card = 5}) → Fin 9 :=
    Sum.elim op861_five_pick op861_five_pick
  have hc : ∀ (S T : {S : Finset (Fin 9) // S.card = 5}),
      (S.1 ∩ T.1).card ≤ 2 → op861_five_pick S ≠ op861_five_pick T := by
    intro S T hadj heq
    have hs := op861_five_pick_spec S
    have ht := op861_five_pick_spec T
    rw [← heq] at ht
    have hlarge := op861_five_common S.1 T.1 (op861_five_pick S) hs.1 ht.1 hs.2 ht.2
    omega
  have hv : ∀ {v w}, (bipartite_subset_graph 5 2).Adj v w → col v ≠ col w := by
    intro v w hv
    cases v with
    | inl S =>
      cases w with
      | inl T => exact False.elim hv
      | inr T => exact hc S T hv
    | inr T =>
      cases w with
      | inl S => exact (hc S T hv).symm
      | inr U => exact False.elim hv
  let C : (bipartite_subset_graph 5 2).Coloring (Fin 9) := SimpleGraph.Coloring.mk col hv
  refine ⟨C, ?_⟩
  intro v
  cases v with
  | inl S => exact (op861_five_pick_spec S).1
  | inr T => exact (op861_five_pick_spec T).1
