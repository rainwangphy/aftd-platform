import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcome
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequence
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateAllocCardEq
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateAllocMono
import AFTD.Kb.GameTheoryEconomics.RoundRobinSequenceGetElemEq
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateSuccStep
import AFTD.Kb.GameTheoryEconomics.PickingPrefixStateCardDiffStepOfNe
import AFTD.Kb.GameTheoryEconomics.PickingPrefixTwoNamedFirstDevBundle
import AFTD.Kb.GameTheoryEconomics.RoundRobinTwoMulAddOneWindowTrace
import AFTD.Kb.GameTheoryEconomics.RoundRobinTwoMulAddOneOutcomeStructure
import AFTD.Kb.GameTheoryEconomics.RoundRobinTwoMulAddOneCoverPairs
import AFTD.Kb.GameTheoryEconomics.PickingSequenceOutcomePairwiseDisjoint
import AFTD.Kb.GameTheoryEconomics.PickingPrefixState

/-!
# round_robin_two_mul_add_one_deviation_certificate

Topic: fair_division   Node: 905e358e273b

Provenance: helper lemma. step for round_robin_pne_envy_zero_ef1_of_two_mul_add_one (research thread RT-3, the threshold question from arXiv:2610.23686 Proposition 1)

Round-Robin with n agents and 2n+1 goods, any reports, agent i ≠ 0: for some good g of agent 0's bundle B_0 (its first pick a1), either some deviation r of agent i alone gets i all of B_0 ∖ {g}, or two deviations r1, r2 of agent i give bundles D1, D2 that together cover B_i + (B_0 ∖ {g}) with multiplicity (every good counted in B_i and in B_0 ∖ {g} is counted at least as often in D1 and D2). A valuation-free certificate for EF1 of i towards agent 0 at an equilibrium.
-/

private lemma indicator_cover (P Q R S : Prop) [Decidable P] [Decidable Q]
    [Decidable R] [Decidable S] (hd : ¬(P ∧ Q)) (hc : P ∨ Q → R ∨ S) :
    (if P then 1 else 0) + (if Q then 1 else 0) ≤
      (if R then 1 else 0) + (if S then 1 else 0 : ℕ) := by
  by_cases hP : P <;> by_cases hQ : Q <;> by_cases hR : R <;> by_cases hS : S <;>
    simp_all

theorem round_robin_two_mul_add_one_deviation_certificate (n : ℕ) [NeZero n]
    (rank : Fin n → Fin (2 * n + 1) ≃ Fin (2 * n + 1)) (i : Fin n) (hi : i ≠ 0) :
    ∃ g ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0,
      (∃ r : Fin (2 * n + 1) ≃ Fin (2 * n + 1),
        picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0 \ {g} ⊆
          picking_sequence_outcome (round_robin_sequence n (2 * n + 1))
            (Function.update rank i r) i) ∨
      (∃ r₁ r₂ : Fin (2 * n + 1) ≃ Fin (2 * n + 1), ∀ x : Fin (2 * n + 1),
        (if x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank i then 1 else 0) +
          (if x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1)) rank 0 \ {g}
            then 1 else 0) ≤
        (if x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1))
            (Function.update rank i r₁) i then 1 else 0) +
          (if x ∈ picking_sequence_outcome (round_robin_sequence n (2 * n + 1))
            (Function.update rank i r₂) i then 1 else 0 : ℕ)) := by
  classical
  obtain ⟨a2,a3,b1,b2,hf2,hm2,hf3,hm3,hB0,hBi,h02,h03,h23,h12,_,_⟩ :=
    round_robin_two_mul_add_one_outcome_structure n rank i hi
  let a1 := rank 0 ⟨0,by omega⟩
  have hremove : picking_sequence_outcome (round_robin_sequence n (2*n+1)) rank 0 \ {a1} =
      {a2,a3} := by
    rw [hB0]
    ext x
    simp only [Finset.mem_sdiff,Finset.mem_insert,Finset.mem_singleton]
    dsimp only [a1]
    aesop
  refine ⟨a1,?_,?_⟩
  · rw [hB0]
    exact Finset.mem_insert_self _ _
  rcases round_robin_two_mul_add_one_cover_pairs n rank i hi a1 a2 a3 b1 b2 rfl ⟨hf2,hm2⟩ ⟨hf3,hm3⟩
    hB0 hBi ⟨h02,h03,h23⟩ with ⟨r,hr⟩ | ⟨r₁,r₂,hr⟩
  · exact Or.inl ⟨r,by rw [hremove]; exact hr⟩
  · refine Or.inr ⟨r₁,r₂,?_⟩
    have hcov : picking_sequence_outcome (round_robin_sequence n (2*n+1)) rank i ∪
        (picking_sequence_outcome (round_robin_sequence n (2*n+1)) rank 0 \ {a1}) ⊆
        picking_sequence_outcome (round_robin_sequence n (2*n+1)) (Function.update rank i r₁) i ∪
        picking_sequence_outcome (round_robin_sequence n (2*n+1)) (Function.update rank i r₂) i := by
      rw [hBi,hremove]
      intro x hx
      apply hr
      simp only [Finset.mem_union,Finset.mem_insert,Finset.mem_singleton] at hx ⊢
      tauto
    have hd := picking_sequence_outcome_pairwise_disjoint (round_robin_sequence n (2*n+1)) rank hi
    intro x
    have hdis : ¬(x ∈ picking_sequence_outcome (round_robin_sequence n (2*n+1)) rank i ∧
        x ∈ picking_sequence_outcome (round_robin_sequence n (2*n+1)) rank 0 \ {a1}) := by
      rintro ⟨hxi,hx0⟩
      exact Finset.disjoint_left.mp hd hxi (Finset.mem_sdiff.mp hx0).1
    have hc : x ∈ picking_sequence_outcome (round_robin_sequence n (2*n+1)) rank i ∨
        x ∈ picking_sequence_outcome (round_robin_sequence n (2*n+1)) rank 0 \ {a1} →
        x ∈ picking_sequence_outcome (round_robin_sequence n (2*n+1)) (Function.update rank i r₁) i ∨
        x ∈ picking_sequence_outcome (round_robin_sequence n (2*n+1)) (Function.update rank i r₂) i :=
      fun hh => Finset.mem_union.mp (hcov (Finset.mem_union.mpr hh))
    exact indicator_cover _ _ _ _ hdis hc
