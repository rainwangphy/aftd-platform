import AFTD.Prelude
import AFTD.Kb.Tcs.HasStrongElimination
import AFTD.Kb.Tcs.IsCompatibleCollection
import AFTD.Kb.Tcs.CollectionMinNonempty

/-!
# not_strong_elimination_iff_compatible_and_union_min

Topic: combinatorics   Node: 4adb20a80ac5

Provenance: original. Related work: refutes `strong_elimination_iff_compatible_and_union_min`

The statement `strong_elimination_iff_compatible_and_union_min` is false: The statement is false as stated because of the empty set:
If ∅ ∈ C, then `is_compatible_collection C` is trivially satisfied by picking C3 = ∅ for any distinct C1, C2 ∈ C and x ∈ C1 ∩ C2, because ∅ ⊆ (C1 ∪ C2) \ {x}.
Furthermore, the condition `∀ F ∈ C, F.Nonempty → ∃ U ⊆ collection_min_nonempty C, F = U.biUnion id` only constrains nonempty sets and ignores ∅.
However, `has_strong_elimination C` requires finding C3 ∈ C containing y ∈ C1 \ C2, so C3 can never be ∅.

A minimal concrete counterexample is on V = Fin 3 with C = {∅, {0, 1}, {0, 2}}:
- `is_compatible_collection C` holds: the only pair with nonempty intersection is {0, 1} and {0, 2} (meeting at 0), and C3 = ∅ ∈ C is a subset of ({0, 1} ∪ {0, 2}) \ {0} = {1, 2}.
- The nonempty sets of C are {0, 1} and {0, 2}; neither properly contains any other nonempty set in C, so both belong to `collection_min_nonempty C`. Each is thus a union of a subcollection of minimal nonempty sets (namely, the singleton subcollection).
- However, `has_strong_elimination C` fails: taking C1 = {0, 1}, C2 = {0, 2}, x = 0, and y = 1, any C3 ∈ C containing 1 must be {0, 1}, but {0, 1} is not a subset of {1, 2} since 0 ∉ {1, 2}.
-/

theorem not_strong_elimination_iff_compatible_and_union_min : ¬ (∀ {V : Type*} [DecidableEq V] (C : Finset (Finset V)), has_strong_elimination C ↔ is_compatible_collection C ∧ ∀ F ∈ C, F.Nonempty → ∃ U ⊆ collection_min_nonempty C, F = U.biUnion id) := by
  intro H
  let u0 : ULift (Fin 3) := ⟨0⟩
  let u1 : ULift (Fin 3) := ⟨1⟩
  let u2 : ULift (Fin 3) := ⟨2⟩
  have u0_ne_u1 : u0 ≠ u1 := by intro h; injection h with h; revert h; decide
  have u0_ne_u2 : u0 ≠ u2 := by intro h; injection h with h; revert h; decide
  have u1_ne_u2 : u1 ≠ u2 := by intro h; injection h with h; revert h; decide
  let exC : Finset (Finset (ULift (Fin 3))) := {∅, {u0, u1}, {u0, u2}}
  have not_se : ¬ has_strong_elimination exC := by
    intro h
    have h1 : ({u0, u1} : Finset (ULift (Fin 3))) ∈ exC := by simp [exC]
    have h2 : ({u0, u2} : Finset (ULift (Fin 3))) ∈ exC := by simp [exC]
    have hx : u0 ∈ ({u0, u1} : Finset (ULift (Fin 3))) ∩ {u0, u2} := by simp
    have hy : u1 ∈ ({u0, u1} : Finset (ULift (Fin 3))) \ {u0, u2} := by
      simp [u1_ne_u2, (u0_ne_u1).symm]
    rcases h _ h1 _ h2 u0 hx u1 hy with ⟨C3, hC3_mem, hy_in, hC3_sub⟩
    simp only [exC, Finset.mem_insert, Finset.mem_singleton] at hC3_mem
    rcases hC3_mem with rfl | rfl | rfl
    · simp at hy_in
    · have h_in : u0 ∈ ({u0, u1} : Finset (ULift (Fin 3))) := by simp
      have := hC3_sub h_in
      simp [u0_ne_u1, u0_ne_u2] at this
    · have : u1 ∈ ({u0, u2} : Finset (ULift (Fin 3))) := hy_in
      simp [u1_ne_u2, (u0_ne_u1).symm] at this
  have is_compat : is_compatible_collection exC := by
    intro C1 h1 C2 h2 hne x hx
    simp only [exC, Finset.mem_insert, Finset.mem_singleton] at h1 h2
    rcases h1 with rfl | rfl | rfl <;> rcases h2 with rfl | rfl | rfl
    · contradiction
    · simp at hx
    · simp at hx
    · simp at hx
    · contradiction
    · refine ⟨∅, by simp [exC], Finset.empty_subset _⟩
    · simp at hx
    · refine ⟨∅, by simp [exC], Finset.empty_subset _⟩
    · contradiction
  have min_01 : ({u0, u1} : Finset (ULift (Fin 3))) ∈ collection_min_nonempty exC := by
    simp only [collection_min_nonempty, Finset.mem_filter, exC, Finset.mem_insert,
               Finset.mem_singleton]
    refine ⟨by simp, ⟨⟨u0, by simp⟩, ?_⟩⟩
    intro T hT hTne hTsub
    rcases hT with rfl | rfl | rfl
    · exact False.elim (Finset.not_nonempty_empty hTne)
    · rfl
    · exfalso
      have : u2 ∈ ({u0, u1} : Finset (ULift (Fin 3))) := hTsub (by simp)
      simp [u0_ne_u2.symm, u1_ne_u2.symm] at this
  have min_02 : ({u0, u2} : Finset (ULift (Fin 3))) ∈ collection_min_nonempty exC := by
    simp only [collection_min_nonempty, Finset.mem_filter, exC, Finset.mem_insert,
               Finset.mem_singleton]
    refine ⟨by simp, ⟨⟨u0, by simp⟩, ?_⟩⟩
    intro T hT hTne hTsub
    rcases hT with rfl | rfl | rfl
    · exact False.elim (Finset.not_nonempty_empty hTne)
    · exfalso
      have : u1 ∈ ({u0, u2} : Finset (ULift (Fin 3))) := hTsub (by simp)
      simp [u0_ne_u1.symm, u1_ne_u2] at this
    · rfl
  have union_min : ∀ F ∈ exC, F.Nonempty → ∃ U ⊆ collection_min_nonempty exC, F = U.biUnion id := by
    intro F hF hFne
    simp only [exC, Finset.mem_insert, Finset.mem_singleton] at hF
    rcases hF with rfl | rfl | rfl
    · exact False.elim (Finset.not_nonempty_empty hFne)
    · refine ⟨{ {u0, u1} }, ?_, ?_⟩
      · simp [min_01]
      · simp
    · refine ⟨{ {u0, u2} }, ?_, ?_⟩
      · simp [min_02]
      · simp
  have h := @H (ULift (Fin 3)) _ exC
  have h_rhs : is_compatible_collection exC ∧ ∀ F ∈ exC, F.Nonempty → ∃ U ⊆ collection_min_nonempty exC, F = U.biUnion id :=
    ⟨is_compat, union_min⟩
  exact not_se (h.mpr h_rhs)
