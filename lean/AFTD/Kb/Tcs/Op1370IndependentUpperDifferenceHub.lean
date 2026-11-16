import AFTD.Prelude
import AFTD.Kb.Tcs.Op1370LowerIndependentFibers

/-!
# op1370_independent_upper_difference_hub

Topic: combinatorics   Node: 1a685c2c882d

Provenance: helper lemma. Equality-structure lemma for the balanced-case route to OP-1370, arXiv:2611.12199, Conjecture 4.3.

For two upper-closed families whose complementary lower-closed families attain equality in the uniform correlation inequality, if the first upper family is proper and the second is nonempty, the difference of the second from the first has a member Z such that every member of the difference has a common superset with Z in the difference.
-/

open Finset

lemma op1370_fiber_toggle {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (x : α)
    (h : 𝒜.memberSubfamily x = 𝒜.nonMemberSubfamily x) (S : Finset α) :
    S ∈ 𝒜 ↔ insert x S ∈ 𝒜 := by
  by_cases hx : x ∈ S
  · simp [hx]
  · have hf : S ∈ 𝒜.memberSubfamily x ↔ S ∈ 𝒜.nonMemberSubfamily x := by rw [h]
    simpa only [mem_memberSubfamily, mem_nonMemberSubfamily, hx, not_false_eq_true, and_true] using hf.symm

lemma op1370_fiber_union {α : Type*} [DecidableEq α]
    (𝒜 : Finset (Finset α)) (T : Finset α)
    (h : ∀ x ∈ T, 𝒜.memberSubfamily x = 𝒜.nonMemberSubfamily x) (S : Finset α) :
    S ∈ 𝒜 ↔ S ∪ T ∈ 𝒜 := by
  induction T using Finset.induction_on with
  | empty => simp
  | @insert x T hx ih =>
    have hT : ∀ y ∈ T, 𝒜.memberSubfamily y = 𝒜.nonMemberSubfamily y := by
      intro y hy
      exact h y (Finset.mem_insert_of_mem hy)
    have hx' : 𝒜.memberSubfamily x = 𝒜.nonMemberSubfamily x := h x (Finset.mem_insert_self x T)
    calc
      S ∈ 𝒜 ↔ S ∪ T ∈ 𝒜 := ih hT
      _ ↔ insert x (S ∪ T) ∈ 𝒜 := op1370_fiber_toggle 𝒜 x hx' (S ∪ T)
      _ ↔ S ∪ insert x T ∈ 𝒜 := by rw [Finset.union_insert]

theorem op1370_independent_upper_difference_hub (n : ℕ) (U V : Finset (Finset (Fin n)))
    (hU : IsUpperSet (U : Set (Finset (Fin n))))
    (hV : IsUpperSet (V : Set (Finset (Fin n))))
    (hUproper : ∃ X, X ∉ U) (hVne : V.Nonempty)
    (hEq : (Uᶜ).card * (Vᶜ).card = 2 ^ n * ((Uᶜ) ∩ (Vᶜ)).card) :
    ∃ Z ∈ V, Z ∉ U ∧ ∀ X ∈ V, X ∉ U →
      ∃ W ∈ V, W ∉ U ∧ X ⊆ W ∧ Z ⊆ W := by
  classical
  have hL : IsLowerSet ((Uᶜ : Finset (Finset (Fin n))) : Set (Finset (Fin n))) := by
    simpa only [coe_compl] using (isLowerSet_compl.mpr hU)
  have hM : IsLowerSet ((Vᶜ : Finset (Finset (Fin n))) : Set (Finset (Fin n))) := by
    simpa only [coe_compl] using (isLowerSet_compl.mpr hV)
  let P : Finset (Fin n) := univ.filter fun x =>
    (Vᶜ).memberSubfamily x ≠ (Vᶜ).nonMemberSubfamily x
  have hLfixed : ∀ x ∈ P, (Uᶜ).memberSubfamily x = (Uᶜ).nonMemberSubfamily x := by
    intro x hx
    have hx' := (mem_filter.mp hx).2
    exact (op1370_lower_independent_fibers n (Uᶜ) (Vᶜ) hL hM hEq x).resolve_right hx'
  have hMfixed : ∀ x ∈ Pᶜ, (Vᶜ).memberSubfamily x = (Vᶜ).nonMemberSubfamily x := by
    intro x hx
    have hnot : x ∉ P := mem_compl.mp hx
    by_contra hne
    exact hnot (mem_filter.mpr ⟨mem_univ x, hne⟩)
  obtain ⟨X, hX⟩ := hUproper
  have hUempty : (∅ : Finset (Fin n)) ∉ U := by
    intro h
    exact hX (hU (Finset.empty_subset X) h)
  obtain ⟨Y, hY⟩ := hVne
  have hVtop : (univ : Finset (Fin n)) ∈ V := hV (subset_univ Y) hY
  have hPnotU : P ∉ U := by
    have h := op1370_fiber_union (Uᶜ) P hLfixed (∅ : Finset (Fin n))
    have he : (∅ : Finset (Fin n)) ∈ Uᶜ := by simpa using hUempty
    have : P ∈ Uᶜ := by simpa using h.mp he
    simpa using this
  have hPinV : P ∈ V := by
    have h := op1370_fiber_union (Vᶜ) Pᶜ hMfixed P
    have ht : (univ : Finset (Fin n)) ∉ Vᶜ := by simpa using hVtop
    have hp : P ∉ Vᶜ := by
      intro hp
      apply ht
      simpa using h.mp hp
    simpa using hp
  refine ⟨P, hPinV, hPnotU, ?_⟩
  intro X hXV hXU
  refine ⟨X ∪ P, hV (subset_union_left) hXV, ?_, subset_union_left, subset_union_right⟩
  have h := op1370_fiber_union (Uᶜ) P hLfixed X
  have hX' : X ∈ Uᶜ := by simpa using hXU
  have : X ∪ P ∈ Uᶜ := h.mp hX'
  simpa using this
