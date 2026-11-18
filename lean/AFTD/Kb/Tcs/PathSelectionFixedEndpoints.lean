import AFTD.Prelude
import AFTD.Kb.Tcs.PathEqualCardinalitySetSelection

/-!
# path_selection_fixed_endpoints

Topic: combinatorics   Node: 8cf463cd88ed

Provenance: helper lemma. Endpoint compatibility for the high-color path construction for OP-874, arXiv:2610.41950.

For a finite path of finite sets of equal cardinality and prescribed elements x and y of its first and last sets, a selection exists from x to y such that each next selection lying in the previous set equals the previous selection if and only if any occurrence of y in every set forces x = y.
-/

theorem path_selection_fixed_endpoints {Ω : Type*} [DecidableEq Ω]
    (P : ℕ → Finset Ω) (hcard : ∀ i, (P i).card = (P (i+1)).card)
    (x : Ω) (hx : x ∈ P 0) (n : ℕ) (y : Ω) (hy : y ∈ P n) :
    (∃ f : ℕ → Ω, f 0 = x ∧ f n = y ∧ (∀ i ≤ n, f i ∈ P i) ∧
      (∀ i < n, f (i+1) ∈ P i → f (i+1) = f i)) ↔
    ((∀ i ≤ n, y ∈ P i) → x = y) := by
  classical
  constructor
  · rintro ⟨f, hf0, hfn, _, hfstep⟩ hall
    by_contra hxy
    have hprop : ∀ i, i ≤ n → f i ≠ y := by
      intro i
      induction i with
      | zero =>
        intro _ h
        apply hxy
        simpa [hf0] using h
      | succ i ih =>
        intro hi h
        have heq := hfstep i (by omega) (by simpa [h] using hall i (by omega))
        exact ih (by omega) (heq.symm.trans h)
    exact hprop n (by omega) hfn
  · intro hcondition
    induction n generalizing y with
    | zero =>
      have hxy := hcondition (by
        intro i hi
        have heq : i = 0 := by omega
        simpa [heq] using hy)
      refine ⟨fun _ => x, rfl, ?_, ?_, ?_⟩
      · exact hxy
      · intro i hi
        have heq : i = 0 := by omega
        simpa [heq] using hx
      · intro i hi; omega
    | succ n ih =>
      by_cases hmem : y ∈ P n
      · have hcond : (∀ i ≤ n, y ∈ P i) → x = y := by
          intro h
          apply hcondition
          intro i hi
          by_cases heq : i = n+1
          · simpa [heq] using hy
          · exact h i (by omega)
        obtain ⟨f, hf0, hfn, hfmem, hfstep⟩ := ih y hmem hcond
        refine ⟨Function.update f (n+1) y, ?_, ?_, ?_, ?_⟩
        · simpa using hf0
        · simp
        · intro i hi
          by_cases heq : i = n+1
          · simpa [heq] using hy
          · simpa [Function.update_of_ne heq] using hfmem i (by omega)
        · intro i hi
          by_cases heq : i = n
          · subst i
            simp only [Function.update_self, Function.update_of_ne (by omega : n ≠ n+1)]
            intro _
            exact hfn.symm
          · have h1 : i+1 ≠ n+1 := by omega
            have h2 : i ≠ n+1 := by omega
            simpa [Function.update_of_ne h1, Function.update_of_ne h2] using hfstep i (by omega)
      · obtain ⟨f, hf0, hfmem, hfstep⟩ := path_equal_cardinality_set_selection P hcard x hx n
        refine ⟨Function.update f (n+1) y, ?_, ?_, ?_, ?_⟩
        · simpa using hf0
        · simp
        · intro i hi
          by_cases heq : i = n+1
          · simpa [heq] using hy
          · simpa [Function.update_of_ne heq] using hfmem i (by omega)
        · intro i hi
          by_cases heq : i = n
          · subst i
            simp only [Function.update_self, Function.update_of_ne (by omega : n ≠ n+1)]
            intro h
            exact (hmem h).elim
          · have h1 : i+1 ≠ n+1 := by omega
            have h2 : i ≠ n+1 := by omega
            simpa [Function.update_of_ne h1, Function.update_of_ne h2] using hfstep i (by omega)
