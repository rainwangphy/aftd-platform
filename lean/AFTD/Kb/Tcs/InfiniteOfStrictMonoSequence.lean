import AFTD.Prelude

/-!
# infinite_of_strict_mono_sequence

Topic: combinatorics   Node: 27887fd6ac91

Provenance: helper lemma. step towards op_939_optimal_upper_density_strictly_greater

If S_n is an ascending sequence of sets where each step adds at least one new element, then the union of S_n is infinite.
-/

/-- If S_n is an ascending sequence of sets where each step adds at least one new element, then the union of S_n is infinite. -/
theorem infinite_of_strict_mono_sequence (S : ℕ → Set ℕ)
    (h_mono : ∀ n, S n ⊆ S (n + 1)) (h_strict : ∀ n, ∃ y ∈ S (n + 1), y ∉ S n) :
    (⋃ n, S n).Infinite := by
  let f : ℕ → ℕ := fun n => Classical.choose (h_strict n)
  have hf_mem : ∀ n, f n ∈ S (n + 1) := fun n => (Classical.choose_spec (h_strict n)).1
  have hf_not : ∀ n, f n ∉ S n := fun n => (Classical.choose_spec (h_strict n)).2
  have hSmono : Monotone S := monotone_nat_of_le_succ h_mono
  refine Set.infinite_of_injective_forall_mem (f := f) ?_ ?_
  · intro m n hmn
    rcases lt_trichotomy m n with hlt | heq | hgt
    · have hmS : f m ∈ S n := hSmono (Nat.succ_le_of_lt hlt) (hf_mem m)
      exact absurd (hmn ▸ hmS) (hf_not n)
    · exact heq
    · have hnS : f n ∈ S m := hSmono (Nat.succ_le_of_lt hgt) (hf_mem n)
      exact absurd (hmn.symm ▸ hnS) (hf_not m)
  · intro n
    exact Set.mem_iUnion_of_mem (n + 1) (hf_mem n)
