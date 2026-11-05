import AFTD.Prelude

/-!
# anti_ramsey_k5_lower_bound_nineteen

Topic: combinatorics   Node: f7aca2e5d969

Provenance: formalization of a published result. Source: arXiv:2611.03878 Theorem 3.2

There exists a symmetric 3-edge-coloring of the complete graph K_19 on vertices ZMod 19 such that every 5-element vertex subset contains at least one edge of each of the three colors, implying that the three-colored anti-Ramsey number satisfies xi(K_5) >= 19.
-/

def anti_ramsey_k5_lower_bound_nineteen_c (x y : ZMod 19) : Fin 3 :=
  let d := x - y
  if d = 1 ∨ d = 18 ∨ d = 7 ∨ d = 12 ∨ d = 8 ∨ d = 11 then 0
  else if d = 2 ∨ d = 17 ∨ d = 3 ∨ d = 16 ∨ d = 5 ∨ d = 14 then 1
  else 2

def anti_ramsey_k5_lower_bound_nineteen_univ : List (ZMod 19) :=
  [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18]

def anti_ramsey_k5_lower_bound_nineteen_check_list (l : List (ZMod 19)) : Bool :=
  ([0, 1, 2] : List (Fin 3)).all fun col =>
    l.any fun u =>
      l.any fun v =>
        decide (u ≠ v) && decide (anti_ramsey_k5_lower_bound_nineteen_c u v = col)

def anti_ramsey_k5_lower_bound_nineteen_check_all_sublists : Bool :=
  (List.sublistsLen 5 anti_ramsey_k5_lower_bound_nineteen_univ).all
    anti_ramsey_k5_lower_bound_nineteen_check_list

set_option maxRecDepth 500000 in
set_option maxHeartbeats 4000000 in
theorem anti_ramsey_k5_lower_bound_nineteen_check_all_sublists_eq :
    anti_ramsey_k5_lower_bound_nineteen_check_all_sublists = true := by
  rfl

theorem anti_ramsey_k5_lower_bound_nineteen_c_symm (x y : ZMod 19) :
    anti_ramsey_k5_lower_bound_nineteen_c x y = anti_ramsey_k5_lower_bound_nineteen_c y x := by
  revert x y
  decide

theorem anti_ramsey_k5_lower_bound_nineteen_univ_toFinset :
    anti_ramsey_k5_lower_bound_nineteen_univ.toFinset = Finset.univ := by
  ext x
  simp only [List.mem_toFinset, Finset.mem_univ, iff_true]
  revert x
  decide

theorem anti_ramsey_k5_lower_bound_nineteen_filter_length_eq_card (s : Finset (ZMod 19)) :
    (anti_ramsey_k5_lower_bound_nineteen_univ.filter (· ∈ s)).length = s.card := by
  have h_nodup : anti_ramsey_k5_lower_bound_nineteen_univ.Nodup := by decide
  have h_toFinset : (anti_ramsey_k5_lower_bound_nineteen_univ.filter (· ∈ s)).toFinset = s := by
    ext x
    simp only [List.mem_toFinset, List.mem_filter, decide_eq_true_eq]
    constructor
    · rintro ⟨-, hx⟩; exact hx
    · intro hx
      refine ⟨?_, hx⟩
      have : x ∈ anti_ramsey_k5_lower_bound_nineteen_univ.toFinset := by
        simp [anti_ramsey_k5_lower_bound_nineteen_univ_toFinset]
      exact List.mem_toFinset.mp this
  rw [← List.toFinset_card_of_nodup (h_nodup.filter _)]
  rw [h_toFinset]

theorem anti_ramsey_k5_lower_bound_nineteen_check_list_prop
    {l : List (ZMod 19)} (h : anti_ramsey_k5_lower_bound_nineteen_check_list l = true) (col : Fin 3) :
    ∃ u ∈ l, ∃ v ∈ l, u ≠ v ∧ anti_ramsey_k5_lower_bound_nineteen_c u v = col := by
  have hcol : col ∈ ([0, 1, 2] : List (Fin 3)) := by
    fin_cases col <;> simp
  rw [anti_ramsey_k5_lower_bound_nineteen_check_list, List.all_eq_true] at h
  have h_any := h col hcol
  rw [List.any_eq_true] at h_any
  rcases h_any with ⟨u, hu, hu_prop⟩
  rw [List.any_eq_true] at hu_prop
  rcases hu_prop with ⟨v, hv, hv_prop⟩
  simp only [Bool.and_eq_true, decide_eq_true_iff] at hv_prop
  exact ⟨u, hu, v, hv, hv_prop.1, hv_prop.2⟩

/-- There exists a three-edge-coloring of K_19 such that every complete subgraph on 5 vertices represents all three colors, showing xi(K_5) >= 19. -/
theorem anti_ramsey_k5_lower_bound_nineteen :
    ∃ c : ZMod 19 → ZMod 19 → Fin 3,
      (∀ x y, c x y = c y x) ∧
      ∀ s : Finset (ZMod 19), s.card = 5 →
        ∀ col : Fin 3, ∃ u ∈ s, ∃ v ∈ s, u ≠ v ∧ c u v = col := by
  use anti_ramsey_k5_lower_bound_nineteen_c
  refine ⟨anti_ramsey_k5_lower_bound_nineteen_c_symm, ?_⟩
  intro s hs col
  let l := anti_ramsey_k5_lower_bound_nineteen_univ.filter (· ∈ s)
  have hl_sub : l.Sublist anti_ramsey_k5_lower_bound_nineteen_univ := List.filter_sublist
  have hl_len : l.length = 5 := by
    rw [← hs]
    exact anti_ramsey_k5_lower_bound_nineteen_filter_length_eq_card s
  have hl_mem : l ∈ List.sublistsLen 5 anti_ramsey_k5_lower_bound_nineteen_univ := by
    rw [List.mem_sublistsLen]
    exact ⟨hl_sub, hl_len⟩
  have h_all : anti_ramsey_k5_lower_bound_nineteen_check_all_sublists = true :=
    anti_ramsey_k5_lower_bound_nineteen_check_all_sublists_eq
  have hl_check : anti_ramsey_k5_lower_bound_nineteen_check_list l = true := by
    rw [anti_ramsey_k5_lower_bound_nineteen_check_all_sublists, List.all_eq_true] at h_all
    exact h_all l hl_mem
  rcases anti_ramsey_k5_lower_bound_nineteen_check_list_prop hl_check col with ⟨u, hu, v, hv, huv, hcol⟩
  rw [List.mem_filter] at hu hv
  simp only [decide_eq_true_eq] at hu hv
  exact ⟨u, hu.2, v, hv.2, huv, hcol⟩
