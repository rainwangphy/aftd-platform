import AFTD.Prelude
import AFTD.Kb.Tcs.IsFeasiblePacking
import AFTD.Kb.Tcs.MultisetPackingNumber
import AFTD.Kb.Tcs.IncidentEdgeMultiset

/-!
# op_1627_maximum_local_packing_realizable

Topic: combinatorics   Node: 49d6bd2cacab

Provenance: formalization of a published result. Source: arXiv:2611.15376 Sec. 7, after Question 7.2

There exist natural numbers r, s, t, n, D satisfying 1 ≤ t ∧ t ≤ s ∧ s ≤ r ∧ 2 ≤ n such that D is even, D = multiset_packing_number r s t (n - 1), for every multiset M of subsets of Fin r, if M is a feasible packing for parameters (r, s, t, n - 1) and M.card = D, then not every block S has even multiplicity M.count S in M, and there exists an edge-coloring ϕ : (⊤ : SimpleGraph (Fin (D + 1))).edgeSet → Finset (Fin r) assigning an s-element subset of Fin r to each edge of the complete graph on Fin (D + 1) such that for every vertex v : Fin (D + 1), the multiset of incident edge labels incident_edge_multiset ϕ v is a feasible packing for parameters (r, s, t, n - 1).
-/

open Finset

private lemma op_1627_sum_filter_card (M : Multiset (Finset (Fin 3))) :
    (∑ x : Fin 3, (M.filter (fun T => x ∈ T)).card) = (M.map Finset.card).sum := by
  induction M using Multiset.induction with
  | empty => simp
  | cons S M ih =>
    rw [Multiset.map_cons, Multiset.sum_cons]
    have hterm : ∀ x : Fin 3,
        (Multiset.filter (fun T => x ∈ T) (S ::ₘ M)).card
          = (Multiset.filter (fun T => x ∈ T) M).card + (if x ∈ S then 1 else 0) := by
      intro x
      by_cases hx : x ∈ S
      · rw [Multiset.filter_cons_of_pos (p := fun T => x ∈ T) (a := S) M hx,
            Multiset.card_cons, if_pos hx, Nat.add_comm]
      · rw [Multiset.filter_cons_of_neg (p := fun T => x ∈ T) (a := S) M hx,
            if_neg hx, Nat.add_zero]
    simp only [hterm]
    rw [Finset.sum_add_distrib, ← ih]
    have hif : (∑ x : Fin 3, (if x ∈ S then 1 else 0)) = S.card := by
      rw [← Finset.card_filter (s := Finset.univ) (p := fun x => x ∈ S)]
      congr 1
      ext x; simp
    rw [hif]
    exact Nat.add_comm _ _

private lemma op_1627_map_card_sum (M : Multiset (Finset (Fin 3)))
    (hcard : ∀ S ∈ M, S.card = 2) : (M.map Finset.card).sum = 2 * M.card := by
  have h1 : M.map Finset.card = M.map (Function.const (Finset (Fin 3)) 2) :=
    Multiset.map_congr rfl (fun S hS => hcard S hS)
  rw [h1, Multiset.map_const, Multiset.sum_replicate]
  simp [Nat.mul_comm]

private lemma op_1627_packing_bound (M : Multiset (Finset (Fin 3)))
    (h : is_feasible_packing 3 2 1 3 M) : M.card ≤ 4 := by
  obtain ⟨hcard, hdeg⟩ := h
  have key := op_1627_sum_filter_card M
  have hb : ∀ x : Fin 3, (M.filter (fun T => x ∈ T)).card ≤ 3 := by
    intro x
    have := hdeg {x} (by simp)
    simpa using this
  have hle : (∑ x : Fin 3, (M.filter (fun T => x ∈ T)).card) ≤ 9 := by
    calc (∑ x : Fin 3, (M.filter (fun T => x ∈ T)).card) ≤ ∑ _x : Fin 3, 3 :=
          Finset.sum_le_sum (fun x _ => hb x)
      _ = 9 := by norm_num
  rw [key, op_1627_map_card_sum M hcard] at hle
  omega

private lemma op_1627_filter_even (M : Multiset (Finset (Fin 3)))
    (h : ∀ S, Even (M.count S)) (x : Fin 3) :
    Even ((M.filter (fun T => x ∈ T)).card) := by
  rw [← Multiset.sum_count_eq_card (s := Finset.univ) (m := M.filter (fun T => x ∈ T)) (by simp)]
  apply Finset.even_sum
  intro S _
  rw [Multiset.count_filter]
  split_ifs with hx
  · exact h S
  · exact ⟨0, rfl⟩

private lemma op_1627_no_even_max (M : Multiset (Finset (Fin 3)))
    (h : is_feasible_packing 3 2 1 3 M) (hcard4 : M.card = 4) :
    ¬ (∀ S, Even (M.count S)) := by
  intro hall
  obtain ⟨hcard, hdeg⟩ := h
  have key := op_1627_sum_filter_card M
  have hb : ∀ x : Fin 3, (M.filter (fun T => x ∈ T)).card ≤ 2 := by
    intro x
    have hle3 : (M.filter (fun T => x ∈ T)).card ≤ 3 := by
      have := hdeg {x} (by simp); simpa using this
    obtain ⟨k, hk⟩ := op_1627_filter_even M hall x
    omega
  have hle : (∑ x : Fin 3, (M.filter (fun T => x ∈ T)).card) ≤ 6 := by
    calc (∑ x : Fin 3, (M.filter (fun T => x ∈ T)).card) ≤ ∑ _x : Fin 3, 2 :=
          Finset.sum_le_sum (fun x _ => hb x)
      _ = 6 := by norm_num
  rw [key, op_1627_map_card_sum M hcard, hcard4] at hle
  omega

private abbrev op_1627_witness : Multiset (Finset (Fin 3)) :=
  {({0, 1} : Finset (Fin 3)), ({0, 1} : Finset (Fin 3)), ({0, 2} : Finset (Fin 3)), ({1, 2} : Finset (Fin 3))}

private def op_1627_edge_label (u v : Fin 5) : Finset (Fin 3) :=
  if (u = 0 ∧ v = 1) ∨ (u = 1 ∧ v = 0) then {1, 2}
  else if (u = 0 ∧ v = 2) ∨ (u = 2 ∧ v = 0) then {0, 2}
  else if (u = 0 ∧ v = 3) ∨ (u = 3 ∧ v = 0) then {0, 1}
  else if (u = 0 ∧ v = 4) ∨ (u = 4 ∧ v = 0) then {0, 1}
  else if (u = 1 ∧ v = 2) ∨ (u = 2 ∧ v = 1) then {0, 1}
  else if (u = 1 ∧ v = 3) ∨ (u = 3 ∧ v = 1) then {0, 2}
  else if (u = 1 ∧ v = 4) ∨ (u = 4 ∧ v = 1) then {0, 2}
  else if (u = 2 ∧ v = 3) ∨ (u = 3 ∧ v = 2) then {1, 2}
  else if (u = 2 ∧ v = 4) ∨ (u = 4 ∧ v = 2) then {0, 2}
  else {1, 2}

private lemma op_1627_packing_number_eq : multiset_packing_number 3 2 1 3 = 4 := by
  let S : Set ℕ := {n | ∃ M : Multiset (Finset (Fin 3)), is_feasible_packing 3 2 1 3 M ∧ M.card = n}
  have hmem4 : (4:ℕ) ∈ S :=
    ⟨op_1627_witness, by unfold is_feasible_packing; decide, by decide⟩
  have hbdd : BddAbove S :=
    ⟨4, by rintro b ⟨M, hM, rfl⟩; exact op_1627_packing_bound M hM⟩
  have hne : S.Nonempty := ⟨4, hmem4⟩
  show sSup S = 4
  apply le_antisymm
  · apply csSup_le hne
    rintro b ⟨M, hM, rfl⟩
    exact op_1627_packing_bound M hM
  · exact le_csSup hbdd hmem4

private lemma op_1627_edge_coloring :
    ∃ ϕ : (⊤ : SimpleGraph (Fin (4 + 1))).edgeSet → Finset (Fin 3),
      (∀ e, (ϕ e).card = 2) ∧
      ∀ v : Fin (4 + 1), is_feasible_packing 3 2 1 3 (incident_edge_multiset ϕ v) :=
  ⟨fun e => Sym2.lift ⟨op_1627_edge_label, by decide⟩ e.1, by
    unfold is_feasible_packing
    decide⟩

/-- Open Problem OP-1627: There exist parameters (r, s, t, n) where D = ν(r, s, t; n-1) is even, no maximum multiset has all even multiplicities, and K_{D+1} admits an (r, s)-set-coloring realizing maximum local packings at every vertex. -/
theorem op_1627_maximum_local_packing_realizable :
    ∃ (r s t n D : ℕ),
      1 ≤ t ∧ t ≤ s ∧ s ≤ r ∧ 2 ≤ n ∧ Even D ∧
      D = multiset_packing_number r s t (n - 1) ∧
      (∀ M : Multiset (Finset (Fin r)),
        is_feasible_packing r s t (n - 1) M ∧ M.card = D →
        ¬ (∀ S, Even (M.count S))) ∧
      ∃ ϕ : (⊤ : SimpleGraph (Fin (D + 1))).edgeSet → Finset (Fin r),
        (∀ e, (ϕ e).card = s) ∧
        ∀ v : Fin (D + 1), is_feasible_packing r s t (n - 1) (incident_edge_multiset ϕ v) := by
  refine ⟨3, 2, 1, 4, 4, by norm_num, by norm_num, by norm_num, by norm_num,
    ⟨2, rfl⟩, ?_, ?_, ?_⟩
  · simpa using op_1627_packing_number_eq.symm
  · rintro M ⟨hM, hcard⟩
    exact op_1627_no_even_max M hM hcard
  · simpa using op_1627_edge_coloring
