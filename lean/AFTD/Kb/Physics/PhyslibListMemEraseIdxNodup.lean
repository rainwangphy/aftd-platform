import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.QuotaPopulationMonotoneIncompatibleFourStatesCommonHouse

/-!
# Physlib.List.mem_eraseIdx_nodup

Topic: classical_mechanics   Node: 64450c34526c

Provenance: formalization of a published result. Source: Physlib, `Physlib.List.mem_eraseIdx_nodup`. Lean proof by Joseph Tooby-Smith, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/ForMathlib/List/InsertIdx.lean (Copyright (c) 2024 Joseph Tooby-Smith. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Physlib.List.mem_eraseIdx_nodup
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {n : Nat} in
lemma Physlib.List.mem_eraseIdx_nodup {I : Type} (i : I) :
    (l : List I) → (n : ℕ) → (hn : n < l.length) → (h : List.Nodup l) →
    i ∈ l.eraseIdx n ↔ i ∈ l ∧ i ≠ l[n]
  | [], _, _, _ => by simp
  | a1 :: as, 0, _, h => by
    simp only [List.eraseIdx_zero, List.tail_cons, List.mem_cons, List.getElem_cons_zero, ne_eq]
    by_cases hi : i = a1
    · subst hi
      simp only [List.nodup_cons] at h
      simp [h]
    · simp [hi]
  | a1 :: as, n+1, hn, h => by
    simp only [List.eraseIdx_cons_succ, List.mem_cons, List.getElem_cons_succ, ne_eq]
    simp only [List.nodup_cons] at h
    rw [mem_eraseIdx_nodup i as n (Nat.succ_lt_succ_iff.mp hn) h.2]
    simp_all only [ne_eq]
    obtain ⟨left, right⟩ := h
    apply Iff.intro
    · intro a
      cases a with
      | inl h =>
        subst h
        simp_all only [or_false, true_and]
        apply Aesop.BuiltinRules.not_intro
        intro a
        simp_all only [List.getElem_mem, not_true_eq_false]
      | inr h_1 => simp_all only [or_true, not_false_eq_true, and_self]
    · intro a
      simp_all only [not_false_eq_true, and_true]
