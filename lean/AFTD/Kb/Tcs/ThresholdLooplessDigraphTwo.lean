import AFTD.Prelude
import AFTD.Kb.Tcs.IsThresholdSequence
import AFTD.Kb.Tcs.LooplessDigraphCount
import AFTD.Kb.Tcs.ThresholdLooplessDigraphGeOne

/-!
# threshold_loopless_digraph_two

Topic: graphs   Node: 677a5615e6ac

Provenance: original. Related work: arXiv:2611.02191 Sec. 11.2

For every threshold degree sequence d on 2 vertices, the number of loopless digraphs with in-degree and out-degree equal to d is 1.
-/

open scoped Classical in
lemma threshold_loopless_digraph_two_filter_zero (D : Digraph (Fin 2)) (hloop : ∀ v, ¬ D.Adj v v) :
    (Finset.univ.filter (fun w => D.Adj 0 w)) = if D.Adj 0 1 then {1} else ∅ := by
  ext x
  fin_cases x
  · split_ifs <;> simp [hloop 0]
  · split_ifs <;> simp [*]

open scoped Classical in
lemma threshold_loopless_digraph_two_filter_one (D : Digraph (Fin 2)) (hloop : ∀ v, ¬ D.Adj v v) :
    (Finset.univ.filter (fun w => D.Adj 1 w)) = if D.Adj 1 0 then {0} else ∅ := by
  ext x
  fin_cases x
  · split_ifs <;> simp [*]
  · split_ifs <;> simp [hloop 1]

open scoped Classical in
lemma threshold_loopless_digraph_two_card_zero (D : Digraph (Fin 2)) (hloop : ∀ v, ¬ D.Adj v v) :
    (Finset.univ.filter (fun w => D.Adj 0 w)).card = if D.Adj 0 1 then 1 else 0 := by
  rw [threshold_loopless_digraph_two_filter_zero D hloop]
  split_ifs <;> simp

open scoped Classical in
lemma threshold_loopless_digraph_two_card_one (D : Digraph (Fin 2)) (hloop : ∀ v, ¬ D.Adj v v) :
    (Finset.univ.filter (fun w => D.Adj 1 w)).card = if D.Adj 1 0 then 1 else 0 := by
  rw [threshold_loopless_digraph_two_filter_one D hloop]
  split_ifs <;> simp

open scoped Classical in
lemma threshold_loopless_digraph_two_adj_zero_one (d : Fin 2 → ℕ) (D : Digraph (Fin 2)) (hloop : ∀ v, ¬ D.Adj v v)
    (hdeg : (Finset.univ.filter (fun w => D.Adj 0 w)).card = d 0) :
    D.Adj 0 1 ↔ d 0 = 1 := by
  rw [threshold_loopless_digraph_two_card_zero D hloop] at hdeg
  constructor
  · intro h
    rw [if_pos h] at hdeg
    exact hdeg.symm
  · intro h
    by_contra hc
    rw [if_neg hc] at hdeg
    omega

open scoped Classical in
lemma threshold_loopless_digraph_two_adj_one_zero (d : Fin 2 → ℕ) (D : Digraph (Fin 2)) (hloop : ∀ v, ¬ D.Adj v v)
    (hdeg : (Finset.univ.filter (fun w => D.Adj 1 w)).card = d 1) :
    D.Adj 1 0 ↔ d 1 = 1 := by
  rw [threshold_loopless_digraph_two_card_one D hloop] at hdeg
  constructor
  · intro h
    rw [if_pos h] at hdeg
    exact hdeg.symm
  · intro h
    by_contra hc
    rw [if_neg hc] at hdeg
    omega

open scoped Classical in
lemma threshold_loopless_digraph_two_digraph_eq (d : Fin 2 → ℕ) (D1 D2 : Digraph (Fin 2))
    (hloop1 : ∀ v, ¬ D1.Adj v v) (hdeg1 : ∀ v, (Finset.univ.filter (fun w => D1.Adj v w)).card = d v)
    (hloop2 : ∀ v, ¬ D2.Adj v v) (hdeg2 : ∀ v, (Finset.univ.filter (fun w => D2.Adj v w)).card = d v) :
    D1 = D2 := by
  rcases D1 with ⟨A1⟩
  rcases D2 with ⟨A2⟩
  have heq : A1 = A2 := by
    ext u v
    fin_cases u <;> fin_cases v
    · have hl1 := hloop1 0; have hl2 := hloop2 0; tauto
    · have h1 := threshold_loopless_digraph_two_adj_zero_one d ⟨A1⟩ hloop1 (hdeg1 0)
      have h2 := threshold_loopless_digraph_two_adj_zero_one d ⟨A2⟩ hloop2 (hdeg2 0)
      exact h1.trans h2.symm
    · have h1 := threshold_loopless_digraph_two_adj_one_zero d ⟨A1⟩ hloop1 (hdeg1 1)
      have h2 := threshold_loopless_digraph_two_adj_one_zero d ⟨A2⟩ hloop2 (hdeg2 1)
      exact h1.trans h2.symm
    · have hl1 := hloop1 1; have hl2 := hloop2 1; tauto
  rw [heq]

/-- For n = 2, every threshold degree sequence has D(d) = 1. -/
theorem threshold_loopless_digraph_two (d : Fin 2 → ℕ) (h : is_threshold_sequence d) : loopless_digraph_count d = 1 := by
  classical
  have hge : 1 ≤ loopless_digraph_count d := threshold_loopless_digraph_ge_one 2 d h
  have hle : loopless_digraph_count d ≤ 1 := by
    unfold loopless_digraph_count
    rw [Finset.card_le_one_iff]
    intro D1 D2 h1 h2
    rw [Finset.mem_filter] at h1 h2
    exact threshold_loopless_digraph_two_digraph_eq d D1 D2 h1.2.1 h1.2.2.1 h2.2.1 h2.2.2.1
  omega
