import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetCoverRankRelation

/-!
# condorcet_source_anchored_exchange_obstruction

Topic: social_choice   Node: efe55174fc12

Provenance: helper lemma. IN-391, OP-19 campaign session10, 2026-10-30. Supporting lemmas and precisely scoped method diagnostics for the rank-saturated acyclic-cover route. The main election theorem remains open; no new election bound or novelty is claimed.

There is a forty-vertex rank-compatible S2 relation with injective rankings with six acyclic sets and exactly three memberships per vertex, realizing every three-element activity signature. Same-signature vertices are Pareto incomparable. Chosen activity-set sources satisfy every source-anchored single-index exchange condition, yet the relation fails S3. This refutes sufficiency of that exchange package, not its necessity for an S3 minimum core and not the main conjecture.
-/

open Finset
set_option maxHeartbeats 100000000
set_option maxRecDepth 30000
def condorcet_anchor_gap_sets : Fin 6 → Finset (Fin 40) := ![{0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19},{0,1,2,3,4,5,6,7,20,21,22,23,24,25,26,27,28,29,30,31},{0,1,8,9,10,11,12,13,20,21,22,23,24,25,32,33,34,35,36,37},{2,3,8,9,14,15,16,17,20,21,26,27,28,29,32,33,34,35,38,39},{4,5,10,11,14,15,18,19,22,23,26,27,30,31,32,33,36,37,38,39},{6,7,12,13,16,17,18,19,24,25,28,29,30,31,34,35,36,37,38,39}]
def condorcet_anchor_gap_rank : Fin 6 → Fin 40 → ℕ := ![![0,14,5,6,1,13,17,19,8,12,10,11,2,18,4,9,15,16,3,7,60,61,62,63,64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79],![16,6,13,11,18,1,3,2,48,49,50,51,52,53,54,55,56,57,58,59,9,15,8,14,4,19,7,17,10,12,0,5,72,73,74,75,76,77,78,79],![13,10,42,43,44,45,46,47,16,7,1,17,15,14,54,55,56,57,58,59,12,3,4,2,9,0,66,67,68,69,70,71,11,19,6,8,5,18,78,79],![40,41,17,5,44,45,46,47,2,9,50,51,52,53,1,11,16,6,58,59,3,7,62,63,64,65,13,15,4,14,70,71,12,0,8,10,76,77,18,19],![40,41,42,43,7,11,46,47,48,49,12,4,52,53,18,9,56,57,17,8,60,61,13,15,64,65,10,1,68,69,19,6,2,16,74,75,14,5,3,0],![40,41,42,43,44,45,8,17,48,49,50,51,6,19,54,55,0,1,7,11,60,61,62,63,9,18,66,67,15,2,14,13,72,73,12,5,4,10,3,16]]
def condorcet_anchor_gap_pred : Fin 40 → ℕ := ![953313918976,948131644960,274698883072,218260328448,1021014179841,1017907813120,390842539808,1096291442464,72004423697,89438045208,827821948956,881461301517,383006015505,953482724991,216959029265,191448486169,13102010171,8603585851,391595954193,451662581789,71962477794,3498984680,826849068256,827654374636,377957631584,828862611708,195438492610,52364981195,217992420706,12957437738,545461886720,468168416064,51860603594,208369368307,68735091832,68734305848,275622626364,314223827791,4969399055,52365038415]
def condorcet_anchor_gap_source : Fin 6 → Fin 40 := ![0,30,25,33,39,16]
def condorcet_anchor_gap_relation (a b : Fin 40) : Prop :=
  (condorcet_anchor_gap_pred b).testBit a.val = true
instance : DecidableRel condorcet_anchor_gap_relation := fun a b =>
  inferInstanceAs (Decidable ((condorcet_anchor_gap_pred b).testBit a.val = true))

theorem condorcet_anchor_gap_rank_exact : ∀ a b : Fin 40,
    condorcet_anchor_gap_relation a b ↔ a ≠ b ∧
      ∀ v, a ∈ condorcet_anchor_gap_sets v → b ∈ condorcet_anchor_gap_sets v →
        condorcet_anchor_gap_rank v a < condorcet_anchor_gap_rank v b := by decide

theorem condorcet_anchor_gap_pair_check :
    (∀ a : Fin 40, ¬condorcet_anchor_gap_relation a a) ∧
    (∀ a b : Fin 40, ∃ c, condorcet_anchor_gap_relation c a ∧
      condorcet_anchor_gap_relation c b) := by decide

theorem condorcet_source_anchored_exchange_obstruction :
    ∃ (R : Fin 40 → Fin 40 → Prop) (U : Fin 6 → Finset (Fin 40))
      (p : Fin 6 → Fin 40 → ℕ) (s : Fin 6 → Fin 40),
      (∀ a b, R a b ↔ a ≠ b ∧ ∀ v, a ∈ U v → b ∈ U v → p v a < p v b) ∧
      (∀ v, Function.Injective (p v)) ∧
      (∀ J : Finset (Fin 40), J.card ≤ 2 →
        ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) ∧
      (∀ v, WellFounded (fun a b : {a : Fin 40 // a ∈ U v} => R a.val b.val)) ∧
      (∀ a, (univ.filter fun v => a ∈ U v).card = 3) ∧
      (∀ T : Finset (Fin 6), T.card = 3 → ∃ a : Fin 40, ∀ v, a ∈ U v ↔ v ∈ T) ∧
      (∀ a b : Fin 40, a ≠ b → (∀ v, a ∈ U v ↔ b ∈ U v) →
        ∃ v, a ∈ U v ∧ p v b < p v a) ∧
      (∀ v, s v ∈ U v ∧ ∀ a, a ∈ U v → ¬R a (s v)) ∧
      (∀ a : Fin 40, ∀ j : Fin 6, a ∉ U j →
        ∃ r : Fin 40, R r a ∧ r ∈ U j ∧
          (∀ v, r ∈ U v → a ∈ U v ∨ v = j) ∧
          (∀ v, v ≠ j → a ∉ U v → R r (s v))) ∧
      ¬(∀ J : Finset (Fin 40), J.card ≤ 3 →
        ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) := by
  let R := condorcet_anchor_gap_relation
  let U := condorcet_anchor_gap_sets
  let p := condorcet_anchor_gap_rank
  let s := condorcet_anchor_gap_source
  have hloop : ∀ a, ¬R a a := condorcet_anchor_gap_pair_check.1
  have hpair : ∀ a b, ∃ c, R c a ∧ R c b := condorcet_anchor_gap_pair_check.2
  have hroot : ∀ J : Finset (Fin 40), J.card ≤ 2 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b := by
    intro J hJ
    by_cases h0 : J.card = 0
    · have hJ0 : J = ∅ := card_eq_zero.mp h0
      subst J
      exact ⟨0,by simp,by simp⟩
    · by_cases h1 : J.card = 1
      · obtain ⟨a,rfl⟩ := card_eq_one.mp h1
        obtain ⟨c,hca,_⟩ := hpair a a
        refine ⟨c,?_,?_⟩
        · simpa only [mem_singleton] using (fun heq : c = a => hloop a (heq ▸ hca))
        · intro b hb
          have heq : b = a := mem_singleton.mp hb
          subst b
          exact hca
      · have h2 : J.card = 2 := by omega
        obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp h2
        obtain ⟨c,hca,hcb⟩ := hpair a b
        refine ⟨c,?_,?_⟩
        · simp only [mem_insert,mem_singleton,not_or]
          exact ⟨fun heq => hloop a (heq ▸ hca),fun heq => hloop b (heq ▸ hcb)⟩
        · intro d hd
          simp only [mem_insert,mem_singleton] at hd
          rcases hd with rfl | rfl
          · exact hca
          · exact hcb
  have hU : ∀ v, WellFounded (fun a b : {a : Fin 40 // a ∈ U v} => R a.val b.val) := by
    intro v
    refine (measure (fun a : {a : Fin 40 // a ∈ U v} => p v a.val)).wf.mono ?_
    intro a b hab
    exact ((condorcet_anchor_gap_rank_exact a b).mp hab).2 v a.property b.property
  refine ⟨R,U,p,s,condorcet_anchor_gap_rank_exact,?_,hroot,hU,?_,?_,?_,?_,?_,?_⟩
  · decide
  · decide
  · decide
  · decide
  · decide
  · decide
  · intro hthree
    obtain ⟨a,_,ha⟩ := hthree {0,1,16} (by decide)
    have hbad : ∀ a : Fin 40, ¬(R a 0 ∧ R a 1 ∧ R a 16) := by decide
    exact hbad a ⟨ha 0 (by simp),ha 1 (by simp),ha 16 (by simp)⟩
