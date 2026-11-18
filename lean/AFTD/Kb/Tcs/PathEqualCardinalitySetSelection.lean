import AFTD.Prelude
import AFTD.Kb.Tcs.EqualCardinalitySetTransition

/-!
# path_equal_cardinality_set_selection

Topic: combinatorics   Node: 40b9a6dc210a

Provenance: helper lemma. Path part of a cyclic palette selection construction for OP-874, arXiv:2610.41950.

Along any finite path of equal-cardinality finite sets, starting from a chosen element in the first set, one can select an element of each set so that a later selection is either equal to the previous selection or absent from the previous set.
-/

theorem path_equal_cardinality_set_selection {Ω : Type*} [DecidableEq Ω]
    (P : ℕ → Finset Ω) (hcard : ∀ i, (P i).card = (P (i+1)).card)
    (x : Ω) (hx : x ∈ P 0) (n : ℕ) :
    ∃ f : ℕ → Ω, f 0 = x ∧ (∀ i ≤ n, f i ∈ P i) ∧
      (∀ i < n, f (i+1) ∈ P i → f (i+1) = f i) := by
  classical
  induction n with
  | zero =>
    refine ⟨fun _ => x, rfl, ?_, ?_⟩
    · intro i hi
      have : i = 0 := by omega
      simpa [this] using hx
    · intro i hi
      omega
  | succ n ih =>
    obtain ⟨f, hf0, hfmem, hfstep⟩ := ih
    obtain ⟨y, hy, hyrel⟩ := equal_cardinality_set_transition (P n) (P (n+1)) (hcard n) (f n) (hfmem n (by omega))
    refine ⟨Function.update f (n+1) y, ?_, ?_, ?_⟩
    · simpa using hf0
    · intro i hi
      by_cases heq : i = n+1
      · subst i
        simpa using hy
      · have hle : i ≤ n := by omega
        simpa [Function.update_of_ne heq] using hfmem i hle
    · intro i hi
      by_cases heq : i = n
      · subst i
        simp only [Function.update_self, Function.update_of_ne (by omega : n ≠ n+1)]
        intro h
        rcases hyrel with h | h
        · exact h
        · contradiction
      · have hlt : i < n := by omega
        have h1 : i+1 ≠ n+1 := by omega
        have h2 : i ≠ n+1 := by omega
        simpa [Function.update_of_ne h1, Function.update_of_ne h2] using hfstep i hlt
