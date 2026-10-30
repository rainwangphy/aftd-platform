import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetAcyclicHalfCoverSignaturePairsGeSeven
import AFTD.Kb.GameTheoryEconomics.CondorcetHalfCoalitionsPartitionOfIncompatible

/-!
# condorcet_acyclic_half_cover_reciprocal_roots_ge_seven

Topic: social_choice   Node: f9d7c4fb4402

Provenance: helper lemma. IN-380, OP-19 campaign session8, 2026-10-30. General consequence of the IN-372 seven-signature lemma, motivated by product-factor screening9520/9524. ReciprocalRoots.lean checked before official submission. No new election bound or research novelty is claimed.

Suppose an S3 finite directed relation has a positive integer acyclic half-cover. If every vertex is connected by reciprocal arrows to one of c designated roots, and each designated root has a reciprocal neighbor, then c is at least seven. Roots and labels need not be injective. The reciprocal-neighbor hypothesis is explicit; isolated reciprocal vertices are not covered by this representation.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_acyclic_half_cover_reciprocal_roots_ge_seven
    (m n c : ℕ) (hn : 0 < n) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m))
    (hroot : ∀ J : Finset (Fin m), J.card ≤ 3 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hhalf : ∀ a, n ≤ 2 * (univ.filter fun v => a ∈ U v).card)
    (r : Fin c → Fin m) (label : Fin m → Fin c)
    (hpath : ∀ a, Relation.ReflTransGen (fun x y => R x y ∧ R y x) (r (label a)) a)
    (hne : ∀ j, ∃ b, R (r j) b ∧ R b (r j)) :
    7 ≤ c := by
  classical
  have hedge : ∀ a b, R a b → R b a → ∀ v, a ∈ U v ↔ b ∉ U v := by
    intro a b hab hba
    exact (condorcet_half_coalitions_partition_of_incompatible n
      (fun v => a ∈ U v) (fun v => b ∈ U v) (hhalf a) (hhalf b) (by
        intro v ⟨ha,hb⟩
        exact (hU v).asymmetric (a := ⟨a,ha⟩) (b := ⟨b,hb⟩) hab hba)).2.2
  have hprop : ∀ a b, Relation.ReflTransGen (fun x y => R x y ∧ R y x) a b →
      (∀ v, b ∈ U v ↔ a ∈ U v) ∨ (∀ v, b ∈ U v ↔ a ∉ U v) := by
    intro a b hp
    induction hp with
    | refl => exact Or.inl (fun _ => Iff.rfl)
    | @tail b d hp hbd ih =>
      rcases ih with hs|hs
      · right
        intro v
        have hh := hedge d b hbd.2 hbd.1 v
        have hi := hs v
        tauto
      · left
        intro v
        have hh := hedge d b hbd.2 hbd.1 v
        have hi := hs v
        tauto
  let B : Fin n → Fin c → Bool := fun v j => decide (r j ∈ U v)
  have hsign : ∀ a, ∃ b : Bool, ∀ v, a ∈ U v ↔ B v (label a) = b := by
    intro a
    rcases hprop _ _ (hpath a) with hs|hs
    · exact ⟨true,fun v => by simpa only [B, decide_eq_true_eq] using hs v⟩
    · exact ⟨false,fun v => by simpa only [B, decide_eq_false_iff_not] using hs v⟩
  choose sign hsign using hsign
  apply condorcet_acyclic_half_cover_signature_pairs_ge_seven m n c hn R U hroot hU B label sign
  · intro j b
    obtain ⟨t,hrt,htr⟩ := hne j
    let X : Finset (Fin n) := univ.filter fun v => r j ∈ U v
    let Y : Finset (Fin n) := univ.filter fun v => t ∈ U v
    have hd : Disjoint X Y := by
      apply disjoint_left.mpr
      intro v hx hy
      exact (hedge _ _ hrt htr v).mp (mem_filter.mp hx).2 (mem_filter.mp hy).2
    have hle : X.card + Y.card ≤ n := by
      rw [← card_union_of_disjoint hd]
      simpa only [card_univ,Fintype.card_fin] using card_le_univ (X ∪ Y)
    have hX : n ≤ 2 * X.card := hhalf _
    have hY : n ≤ 2 * Y.card := hhalf _
    have hXeq : 2 * X.card = n := by omega
    have hYeq : 2 * Y.card = n := by omega
    cases b
    · have heq : (univ.filter fun v => B v j = false) = Y := by
        ext v
        simp only [Y,mem_filter,mem_univ,true_and,B,decide_eq_false_iff_not]
        have hh := hedge _ _ hrt htr v
        tauto
      rw [heq]
      exact hYeq
    · simpa only [B,decide_eq_true_eq] using hXeq
  · exact hsign
