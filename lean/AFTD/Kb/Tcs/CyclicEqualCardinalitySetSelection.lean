import AFTD.Prelude
import AFTD.Kb.Tcs.EqualCardinalitySetTransition
import AFTD.Kb.Tcs.PathSelectionFixedEndpoints

/-!
# cyclic_equal_cardinality_set_selection

Topic: combinatorics   Node: c631b06d9348

Provenance: helper lemma. Elementary cyclic-selection lemma for the high-color cycle construction investigated for OP-874, arXiv:2610.41950.

For any nonempty cyclic sequence of nonempty finite sets of equal cardinality, one can select an element from each set so that, whenever the next selected element also lies in the current set, the two selected elements agree.
-/

theorem cyclic_equal_cardinality_set_selection {Ω : Type*} [DecidableEq Ω]
    (n : ℕ) [NeZero n] (P : Fin n → Finset Ω)
    (hnonempty : ∀ i, (P i).Nonempty)
    (hcard : ∀ i j, (P i).card = (P j).card) :
    ∃ f : Fin n → Ω,
      (∀ i, f i ∈ P i) ∧
      (∀ i, f (i + 1) ∈ P i → f (i + 1) = f i) := by
  classical
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let first : Fin n := ⟨0, hn⟩
  let last : Fin n := ⟨n - 1, by omega⟩
  let Q : ℕ → Finset Ω := fun j => P ⟨j % n, Nat.mod_lt _ hn⟩
  have hQ : ∀ j, (Q j).card = (Q (j+1)).card := by
    intro j
    apply hcard
  have hQfirst : Q 0 = P first := by
    change P ⟨0 % n, Nat.mod_lt _ hn⟩ = P first
    apply congrArg P
    apply Fin.ext
    simp [first]
  have hQlast : Q (n-1) = P last := by
    change P ⟨(n-1) % n, Nat.mod_lt _ hn⟩ = P last
    apply congrArg P
    apply Fin.ext
    simp [last, Nat.mod_eq_of_lt (by omega : n-1 < n)]
  have hend : ∃ x y : Ω, x ∈ P first ∧ y ∈ P last ∧
      ((∀ j ≤ n-1, y ∈ Q j) → x = y) ∧
      (x ∈ P last → x = y) := by
    by_cases h : ∃ z, z ∈ P first ∧ z ∈ P last
    · obtain ⟨z, hz1, hz2⟩ := h
      exact ⟨z, z, hz1, hz2, by intros; rfl, by intros; rfl⟩
    · obtain ⟨x, hx⟩ := hnonempty first
      obtain ⟨y, hy⟩ := hnonempty last
      have hxlast : x ∉ P last := by
        intro hmem
        exact h ⟨x, hx, hmem⟩
      have hyfirst : y ∉ P first := by
        intro hmem
        exact h ⟨y, hmem, hy⟩
      refine ⟨x, y, hx, hy, ?_, ?_⟩
      · intro hall
        exact (hyfirst (by simpa [hQfirst] using hall 0 (by omega))).elim
      · intro hmem
        exact (hxlast hmem).elim
  obtain ⟨x, y, hx, hy, hcondition, hclose⟩ := hend
  have hxQ : x ∈ Q 0 := by simpa [hQfirst] using hx
  have hyQ : y ∈ Q (n-1) := by simpa [hQlast] using hy
  obtain ⟨f, hf0, hfn, hfmem, hfstep⟩ :=
    (path_selection_fixed_endpoints Q hQ x hxQ (n-1) y hyQ).2 hcondition
  refine ⟨fun i => f i.val, ?_, ?_⟩
  · intro i
    have hj : i.val ≤ n-1 := by have := i.isLt; omega
    have hi : Q i.val = P i := by
      change P ⟨i.val % n, Nat.mod_lt _ hn⟩ = P i
      apply congrArg P
      apply Fin.ext
      exact Nat.mod_eq_of_lt i.isLt
    simpa [hi] using hfmem i.val hj
  · intro i hmem
    by_cases hi : i.val = n-1
    · have hlast : i = last := by apply Fin.ext; simpa [last] using hi
      subst i
      have hwrap : last + 1 = first := by
        apply Fin.ext
        simp [first, last, Fin.val_add, Fin.val_one', Nat.add_mod_mod,
          Nat.sub_add_cancel hn]
      rw [hwrap] at hmem ⊢
      have hxlast : x ∈ P last := by simpa [first, hf0] using hmem
      have hxy := hclose hxlast
      simpa [first, last, hf0, hfn] using hxy
    · have hlt : i.val + 1 < n := by have := i.isLt; omega
      have hval : (i + 1).val = i.val + 1 := Fin.val_add_one_of_lt' hlt
      have hQ_i : Q i.val = P i := by
        change P ⟨i.val % n, Nat.mod_lt _ hn⟩ = P i
        apply congrArg P
        apply Fin.ext
        exact Nat.mod_eq_of_lt i.isLt
      have hstep := hfstep i.val (by omega)
      change f (i + 1).val ∈ P i at hmem
      change f (i + 1).val = f i.val
      rw [hval] at hmem ⊢
      exact hstep (by simpa [hQ_i] using hmem)
