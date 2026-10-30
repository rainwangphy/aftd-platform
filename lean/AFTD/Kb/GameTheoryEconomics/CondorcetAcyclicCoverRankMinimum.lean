import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetAcyclicCoverUniformize
import AFTD.Kb.GameTheoryEconomics.CondorcetAcyclicCoverRankSaturation
import AFTD.Kb.GameTheoryEconomics.CondorcetMinimalRankCoreParetoAntichain
import AFTD.Kb.GameTheoryEconomics.CondorcetCoverRankRelation

/-!
# condorcet_acyclic_cover_rank_minimum

Topic: social_choice   Node: 26afd8637f28

Provenance: helper lemma. IN-391, OP-19 campaign session10, 2026-10-30. Supporting lemmas and precisely scoped method diagnostics for the rank-saturated acyclic-cover route. The main election theorem remains open; no new election bound or novelty is claimed.

For positive q, every finite S_k relation with an n-set acyclic family covering every vertex at least q times yields a trimmed exactly-q family, injective rankings, and a minimum-cardinality induced S_k subset B in the saturated rank relation. B has more than k vertices and the contained-signature Pareto antichain property. No bound on repeated activity types is asserted.
-/

open Finset
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000

theorem condorcet_acyclic_cover_rank_minimum
    (m n k q : ℕ) (hq : 0 < q) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m))
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hcover : ∀ a, q ≤ (univ.filter fun v => a ∈ U v).card) :
    ∃ (V : Fin n → Finset (Fin m)) (p : Fin n → Fin m → ℕ)
      (B : Finset (Fin m)),
      (∀ v, V v ⊆ U v) ∧
      (∀ a, (univ.filter fun v => a ∈ V v).card = q) ∧
      (∀ v, Function.Injective (p v)) ∧
      k < B.card ∧
      (∀ J : Finset (Fin m), J ⊆ B → J.card ≤ k →
        ∃ r, r ∈ B ∧ r ∉ J ∧ ∀ c ∈ J, condorcet_cover_rank_relation V p r c) ∧
      (∀ C : Finset (Fin m),
        (∀ J : Finset (Fin m), J ⊆ C → J.card ≤ k →
          ∃ r, r ∈ C ∧ r ∉ J ∧ ∀ c ∈ J, condorcet_cover_rank_relation V p r c) →
        B.card ≤ C.card) ∧
      (∀ a ∈ B, ∀ b ∈ B, a ≠ b →
        (∀ v, a ∈ V v → b ∈ V v) →
        ∃ v, a ∈ V v ∧ p v b < p v a) := by
  classical
  obtain ⟨V,hVU,hV,hVc⟩ := condorcet_acyclic_cover_uniformize m n q R U hU hcover
  obtain ⟨p,hp,_,hpr⟩ := condorcet_acyclic_cover_rank_saturation m n k R V hroot hV
  let good : Finset (Fin m) → Prop := fun B =>
    ∀ J : Finset (Fin m), J ⊆ B → J.card ≤ k →
      ∃ r, r ∈ B ∧ r ∉ J ∧ ∀ c ∈ J, condorcet_cover_rank_relation V p r c
  let F := univ.filter good
  have huniv : (univ : Finset (Fin m)) ∈ F := by
    refine mem_filter.mpr ⟨mem_univ _,?_⟩
    intro J _ hJ
    obtain ⟨r,hr,hrel⟩ := hpr J hJ
    exact ⟨r,mem_univ _,hr,hrel⟩
  obtain ⟨B,hBF,hBmin⟩ := F.exists_min_image Finset.card ⟨univ,huniv⟩
  have hB : good B := (mem_filter.mp hBF).2
  have hmin : ∀ C : Finset (Fin m), good C → B.card ≤ C.card :=
    fun C hC => hBmin C (mem_filter.mpr ⟨mem_univ _,hC⟩)
  have hcard : k < B.card := by
    by_contra! h
    obtain ⟨a,ha,hanot,_⟩ := hB B (subset_refl _) h
    exact hanot ha
  refine ⟨V,p,B,hVU,hVc,hp,hcard,hB,hmin,?_⟩
  apply condorcet_minimal_rank_core_pareto_antichain V p B _ hB hmin
  intro a _
  have hpos : 0 < (univ.filter fun v => a ∈ V v).card := by rw [hVc]; exact hq
  obtain ⟨v,hv⟩ := card_pos.mp hpos
  exact ⟨v,(mem_filter.mp hv).2⟩
