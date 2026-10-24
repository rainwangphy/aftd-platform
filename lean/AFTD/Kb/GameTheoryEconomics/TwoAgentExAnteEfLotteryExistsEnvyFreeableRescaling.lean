import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AllocationBundle
import AFTD.Kb.GameTheoryEconomics.AllocationIsEnvyFreeable
import AFTD.Kb.GameTheoryEconomics.TwoAgentEnvyFreeableIff

/-!
# two_agent_ex_ante_ef_lottery_exists_envy_freeable_rescaling

Topic: fair_division   Node: 9b3fd496a16c

Provenance: formalization of a published result. Source: arXiv:2610.14994, Theorem 4.1 (first part)

For two agents with arbitrary real valuations over subsets of a finite set of items, if q is an ex-ante envy-free lottery over complete allocations, then for every coordinatewise positive vector c, there exists an allocation in the support of q that is envy-freeable at the rescaled profile c ⊙ v.
-/

open Finset in
lemma two_agent_ex_ante_ef_lottery_exists_envy_freeable_rescaling_helper
    {α : Type*} [Fintype α] (q : α → ℝ) (f : α → ℝ)
    (hq_nonneg : ∀ x, 0 ≤ q x) (hq_sum : ∑ x, q x = 1)
    (h_sum : 0 ≤ ∑ x, q x * f x) :
    ∃ x, 0 < q x ∧ 0 ≤ f x := by
  classical
  by_contra! h
  have h_le : ∀ x, q x * f x ≤ 0 := by
    intro x
    rcases (hq_nonneg x).lt_or_eq with hpos | heq
    · exact mul_nonpos_of_nonneg_of_nonpos (le_of_lt hpos) (le_of_lt (h x hpos))
    · simp [← heq]
  have hex : ∃ x, 0 < q x := by
    by_contra! hq_all
    have : ∑ x, q x ≤ 0 := by
      calc ∑ x, q x ≤ ∑ x : α, (0 : ℝ) := sum_le_sum (fun x _ => hq_all x)
      _ = 0 := by simp
    linarith
  rcases hex with ⟨x0, hx0⟩
  have h_strict : q x0 * f x0 < 0 := mul_neg_of_pos_of_neg hx0 (h x0 hx0)
  have h_other : ∑ x ∈ univ.erase x0, q x * f x ≤ 0 := by
    calc ∑ x ∈ univ.erase x0, q x * f x ≤ ∑ x ∈ univ.erase x0, (0 : ℝ) :=
          sum_le_sum (fun x _ => h_le x)
    _ = 0 := by simp
  have h_tot : ∑ x, q x * f x < 0 := by
    rw [← sum_erase_add (s := univ) (f := fun x => q x * f x) (mem_univ x0)]
    linarith
  linarith

/-- For two agents, every ex-ante envy-free lottery contains in its support an allocation that is envy-freeable under any positive rescaling of valuations. -/
theorem two_agent_ex_ante_ef_lottery_exists_envy_freeable_rescaling
    {M : Type*} [Fintype M] [DecidableEq M]
    (v : Fin 2 → Finset M → ℝ) (q : (M → Fin 2) → ℝ)
    (hq_nonneg : ∀ A, 0 ≤ q A) (hq_sum : ∑ A, q A = 1)
    (hef : ∀ i j, ∑ A, q A * v i (allocation_bundle A j) ≤ ∑ A, q A * v i (allocation_bundle A i))
    (c : Fin 2 → ℝ) (hc : ∀ i, 0 < c i) :
    ∃ A : M → Fin 2, 0 < q A ∧
      allocation_is_envy_freeable (fun i S => c i * v i S) A := by
  open Finset in
  let f : (M → Fin 2) → ℝ := fun A =>
    (c 0 * v 0 (allocation_bundle A 0) - c 0 * v 0 (allocation_bundle A 1)) +
    (c 1 * v 1 (allocation_bundle A 1) - c 1 * v 1 (allocation_bundle A 0))
  have h0 : 0 ≤ c 0 * ((∑ A, q A * v 0 (allocation_bundle A 0)) - (∑ A, q A * v 0 (allocation_bundle A 1))) := by
    apply mul_nonneg (le_of_lt (hc 0))
    linarith [hef 0 1]
  have h1 : 0 ≤ c 1 * ((∑ A, q A * v 1 (allocation_bundle A 1)) - (∑ A, q A * v 1 (allocation_bundle A 0))) := by
    apply mul_nonneg (le_of_lt (hc 1))
    linarith [hef 1 0]
  have hsum_eq : ∑ A, q A * f A =
      c 0 * ((∑ A, q A * v 0 (allocation_bundle A 0)) - (∑ A, q A * v 0 (allocation_bundle A 1))) +
      c 1 * ((∑ A, q A * v 1 (allocation_bundle A 1)) - (∑ A, q A * v 1 (allocation_bundle A 0))) := by
    calc
      ∑ A, q A * f A
        = ∑ A, (c 0 * (q A * v 0 (allocation_bundle A 0)) - c 0 * (q A * v 0 (allocation_bundle A 1)) +
               (c 1 * (q A * v 1 (allocation_bundle A 1)) - c 1 * (q A * v 1 (allocation_bundle A 0)))) := by
          apply Finset.sum_congr rfl; intro A _; dsimp [f]; ring
      _ = (c 0 * ∑ A, q A * v 0 (allocation_bundle A 0) - c 0 * ∑ A, q A * v 0 (allocation_bundle A 1)) +
          (c 1 * ∑ A, q A * v 1 (allocation_bundle A 1) - c 1 * ∑ A, q A * v 1 (allocation_bundle A 0)) := by
          simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
      _ = c 0 * (∑ A, q A * v 0 (allocation_bundle A 0) - ∑ A, q A * v 0 (allocation_bundle A 1)) +
          c 1 * (∑ A, q A * v 1 (allocation_bundle A 1) - ∑ A, q A * v 1 (allocation_bundle A 0)) := by
          ring
  have hf_sum : 0 ≤ ∑ A, q A * f A := by
    rw [hsum_eq]
    linarith
  rcases two_agent_ex_ante_ef_lottery_exists_envy_freeable_rescaling_helper q f hq_nonneg hq_sum hf_sum with ⟨A, hqA, hfA⟩
  use A, hqA
  rw [two_agent_envy_freeable_iff]
  exact hfA
