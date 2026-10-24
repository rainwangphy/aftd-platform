import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.AllocationBundle
import AFTD.Kb.GameTheoryEconomics.AllocationIsEnvyFreeable
import AFTD.Kb.GameTheoryEconomics.TwoAgentExAnteEfLotteryExistsEnvyFreeableRescaling
import AFTD.Kb.GameTheoryEconomics.TwoAgentScaleFreeLotteryOfEnvyFreeableRescalings

/-!
# two_agent_converse_theorem

Topic: fair_division   Node: c9af90824f53

Provenance: formalization of a published result. Source: arXiv:2610.14994 Theorem 4.1

For two agents with arbitrary real valuations over subsets of a finite set of items, if q is an ex-ante envy-free lottery over complete allocations, then for every coordinatewise positive vector c = (c₁, c₂) in ℝ_{>0}², there exists an allocation in the support of q that is envy-freeable at the rescaled profile c ⊙ v; furthermore, for any scale-free allocation property P, an ex-ante envy-free and ex-post P lottery exists if and only if every positive rescaling c ⊙ v admits an allocation that is simultaneously P and envy-freeable.
-/

/-- Theorem 4.1 of arXiv:2610.14994: for two agents, ex-ante envy-freeness guarantees existence of an envy-freeable allocation under every positive rescaling, and an ex-ante envy-free lottery with scale-free property P exists if and only if every positive rescaling admits an envy-freeable P-allocation. -/
theorem two_agent_converse_theorem
    {M : Type*} [Fintype M] [DecidableEq M]
    (v : Fin 2 → Finset M → ℝ) :
    (∀ (q : (M → Fin 2) → ℝ)
       (hq_nonneg : ∀ A, 0 ≤ q A) (hq_sum : ∑ A, q A = 1)
       (hef : ∀ i j, ∑ A, q A * v i (allocation_bundle A j) ≤ ∑ A, q A * v i (allocation_bundle A i))
       (c : Fin 2 → ℝ) (hc : ∀ i, 0 < c i),
       ∃ A : M → Fin 2, 0 < q A ∧
         allocation_is_envy_freeable (fun i S => c i * v i S) A) ∧
    (∀ (P : (Fin 2 → Finset M → ℝ) → (M → Fin 2) → Prop)
       (hP : ∀ (v' : Fin 2 → Finset M → ℝ) (c : Fin 2 → ℝ), (∀ i, 0 < c i) →
         ∀ A, P (fun i S => c i * v' i S) A ↔ P v' A),
       (∃ q : (M → Fin 2) → ℝ, (∀ A, 0 ≤ q A) ∧ ∑ A, q A = 1 ∧
         (∀ i j, ∑ A, q A * v i (allocation_bundle A j) ≤ ∑ A, q A * v i (allocation_bundle A i)) ∧
         (∀ A, 0 < q A → P v A)) ↔
       (∀ c : Fin 2 → ℝ, (∀ i, 0 < c i) →
         ∃ A : M → Fin 2, P (fun i S => c i * v i S) A ∧
           allocation_is_envy_freeable (fun i S => c i * v i S) A)) := by
  constructor
  · intro q hq_nonneg hq_sum hef c hc
    exact two_agent_ex_ante_ef_lottery_exists_envy_freeable_rescaling v q hq_nonneg hq_sum hef c hc
  · intro P hP
    constructor
    · rintro ⟨q, hnn, hsum, hef, hPq⟩ c hc
      obtain ⟨A, hqA, hEF⟩ :=
        two_agent_ex_ante_ef_lottery_exists_envy_freeable_rescaling v q hnn hsum hef c hc
      exact ⟨A, (hP v c hc A).2 (hPq A hqA), hEF⟩
    · intro h
      exact two_agent_scale_free_lottery_of_envy_freeable_rescalings v P hP h
