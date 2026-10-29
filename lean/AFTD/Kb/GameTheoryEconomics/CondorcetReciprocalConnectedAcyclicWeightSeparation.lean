import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetHalfCoalitionsPartitionOfIncompatible
import AFTD.Kb.GameTheoryEconomics.CondorcetDimensionLeThreeIffAcyclicWeightSeparation

/-!
# condorcet_reciprocal_connected_acyclic_weight_separation

Topic: social_choice   Node: 7974be759c16

Provenance: helper lemma. IN-362 structural reduction for OP-19. Standard complementary-coalition propagation combined with the established finite acyclic-cover duality. No new universal election bound or research advance. Background LP: https://dmtcs.episciences.org/6020/pdf .

For any finite directed relation in which every vertex set of size at most two has an outside common predecessor, if the undirected graph of reciprocal arrows is connected, there exist nonnegative real weights putting every induced acyclic subset strictly below half the total. Consequently an S3 relation violating the main weight-separation conjecture must have disconnected reciprocal graph. Oriented relations are not covered. There is no bound on the vertex count.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_reciprocal_connected_no_acyclic_half_cover
    (m n : ℕ) (R : Fin m → Fin m → Prop) (U : Fin n → Finset (Fin m))
    (hn : 0 < n)
    (hpred : ∀ J : Finset (Fin m), J.card ≤ 2 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hconn : ∀ a b, Relation.ReflTransGen (fun x y => R x y ∧ R y x) a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val)) :
    ¬ (∀ a, n ≤ 2 * (univ.filter fun v => a ∈ U v).card) := by
  classical
  intro hhalf
  have hedge : ∀ a b, R a b → R b a → ∀ v, a ∈ U v ↔ b ∉ U v := by
    intro a b hab hba
    exact (condorcet_half_coalitions_partition_of_incompatible n
      (fun v => a ∈ U v) (fun v => b ∈ U v) (hhalf a) (hhalf b) (by
        intro v ⟨ha,hb⟩
        exact (hU v).asymmetric (a := ⟨a,ha⟩) (b := ⟨b,hb⟩) hab hba)).2.2
  obtain ⟨r,_,_⟩ := hpred ∅ (by simp)
  obtain ⟨s,hs,_⟩ := hpred {r} (by simp)
  have hne : r ≠ s := by intro h; apply hs; simp [h]
  obtain ⟨t,hrt,_⟩ := (hconn r s).cases_head.resolve_left hne
  have hex : ∀ a, ∃ v : Fin n, a ∈ U v := by
    intro a
    have hpos : 0 < (univ.filter fun v => a ∈ U v).card := by
      have h := hhalf a
      omega
    obtain ⟨v,hv⟩ := card_pos.mp hpos
    exact ⟨v,(mem_filter.mp hv).2⟩
  obtain ⟨v,hrv⟩ := hex r
  obtain ⟨w,htw⟩ := hex t
  have hrw : r ∉ U w := by
    intro h
    exact (hedge r t hrt.1 hrt.2 w).mp h htw
  have hopp : ∀ a, a ∈ U v ↔ a ∉ U w := by
    intro a
    induction hconn r a with
    | refl => tauto
    | @tail b c hpath hbc ih =>
      have hv := hedge b c hbc.1 hbc.2 v
      have hw := hedge b c hbc.1 hbc.2 w
      tauto
  have hcover : ∀ a, a ∈ U v ∨ a ∈ U w := by
    intro a
    by_cases h : a ∈ U w
    · exact Or.inr h
    · exact Or.inl ((hopp a).mpr h)
  obtain ⟨a,_,hmina⟩ := (hU v).has_min Set.univ ⟨⟨r,hrv⟩,Set.mem_univ _⟩
  obtain ⟨b,_,hminb⟩ := (hU w).has_min Set.univ ⟨⟨t,htw⟩,Set.mem_univ _⟩
  have hcard : ({a.val,b.val} : Finset (Fin m)).card ≤ 2 := by
    have h := card_insert_le a.val ({b.val} : Finset (Fin m))
    simpa only [card_singleton] using h
  obtain ⟨z,_,hz⟩ := hpred {a.val,b.val} hcard
  rcases hcover z with hzv | hzw
  · exact hmina ⟨z,hzv⟩ (Set.mem_univ _) (hz a.val (by simp))
  · exact hminb ⟨z,hzw⟩ (Set.mem_univ _) (hz b.val (by simp))

theorem condorcet_reciprocal_connected_acyclic_weight_separation
    (m : ℕ) (R : Fin m → Fin m → Prop)
    (hpred : ∀ J : Finset (Fin m), J.card ≤ 2 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hconn : ∀ a b, Relation.ReflTransGen (fun x y => R x y ∧ R y x) a b) :
    ∃ w : Fin m → ℝ, (∀ a, 0 ≤ w a) ∧
      ∀ A : Finset (Fin m),
        WellFounded (fun a b : {a : Fin m // a ∈ A} => R a.val b.val) →
        2 * (∑ a ∈ A, w a) < ∑ a, w a := by
  classical
  apply (condorcet_half_cover_acyclic_half_cover_duality m R).mp
  rintro ⟨n,U,hn,hU,hhalf⟩
  exact condorcet_reciprocal_connected_no_acyclic_half_cover m n R U hn hpred hconn hU hhalf
