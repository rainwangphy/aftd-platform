import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetDimensionLeThreeIffAcyclicWeightSeparation

/-!
# condorcet_product_fixed_point_acyclic_mass_obstruction

Topic: social_choice   Node: 9811641ff856

Provenance: helper lemma. IN-357 method diagnostic for the OP-19 weighted acyclic-separation route. Related product fixed-point construction: https://theorydish.blog/2026/09/11/condorcet-quintets-a-proof-from-the-book/ and https://arxiv.org/html/2609.35186 , Section3. The finite relation is a chain of seven vertices reciprocally joined to a reciprocal clique of six. This is a limitation of an arbitrary product fixed point as a pointwise acyclic separator, not an election counterexample, a limitation on optimizing vertex weights, or a new research-level election result. Computation8895 supplied the set-root assignment; all finite claims are checked by the Lean kernel.

There are an irreflexive directed relation on thirteen vertices, a root map on ordered triples, and a seven-vertex induced acyclic subset. Every root is related to each sampled vertex. The map is invariant under permutations of the triple and under the two multiplicity patterns on a two-element underlying set. Each vertex is the root of exactly169 ordered inputs, so uniform iid input has uniform output. The seven-vertex acyclic subset therefore has uniform mass7/13, above half. Nevertheless this same relation has no integer acyclic half-cover for any positive voter count. The relation is allowed to have reciprocal arrows; this theorem makes no oriented or tournament assertion.
-/

open Finset
open scoped BigOperators
set_option maxRecDepth 20000
set_option maxHeartbeats 12000000

def condorcet_acyclic_root_relation (a b : Fin 13) : Prop :=
  a ≠ b ∧ (7 ≤ a.val ∨ 7 ≤ b.val ∨ a.val < b.val)

instance : DecidableRel condorcet_acyclic_root_relation := fun a b =>
  inferInstanceAs (Decidable (a ≠ b ∧ (7 ≤ a.val ∨ 7 ≤ b.val ∨ a.val < b.val)))

def condorcet_acyclic_root_table : Fin 13 → Fin 13 → Fin 13 → Fin 13 :=
  ![![![7,9,7,7,7,7,7,9,9,7,9,9,9],![9,9,7,7,7,7,7,9,9,10,9,10,10],![7,7,7,7,7,7,7,10,10,10,9,10,10],![7,7,7,7,7,7,7,10,10,10,9,10,10],![7,7,7,7,7,7,8,8,10,10,9,10,10],![7,7,7,7,7,7,7,8,10,10,9,10,10],![7,7,7,7,8,7,7,8,10,10,9,10,11],![9,9,10,10,8,8,8,9,9,8,8,8,8],![9,9,10,10,10,10,10,9,9,7,7,7,7],![7,10,10,10,10,10,10,8,7,7,11,10,11],![9,9,9,9,9,9,9,8,7,11,9,9,11],![9,10,10,10,10,10,10,8,7,10,9,9,10],![9,10,10,10,10,10,11,8,7,11,11,10,9]],![![9,9,7,7,7,7,7,9,9,10,9,10,10],![9,0,9,9,9,9,9,9,9,0,9,9,9],![7,9,9,11,11,11,11,11,11,11,11,10,11],![7,9,11,9,11,11,11,11,11,11,11,12,11],![7,9,11,11,9,12,12,12,12,12,12,12,11],![7,9,11,11,12,9,12,12,12,12,12,12,11],![7,9,11,11,12,12,9,12,12,12,12,12,11],![9,9,11,11,12,12,12,9,0,12,12,12,11],![9,9,11,11,12,12,12,0,9,12,12,12,11],![10,0,11,11,12,12,12,12,12,0,12,12,11],![9,9,11,11,12,12,12,12,12,12,9,12,11],![10,9,10,12,12,12,12,12,12,12,12,9,10],![10,9,11,11,11,11,11,11,11,11,11,10,9]],![![7,7,7,7,7,7,7,10,10,10,9,10,10],![7,9,9,11,11,11,11,11,11,11,11,10,11],![7,9,9,1,1,1,1,9,1,1,1,1,1],![7,11,1,1,1,1,1,8,1,1,1,1,8],![7,11,1,1,1,1,1,8,1,8,8,8,8],![7,11,1,1,1,1,1,8,1,8,8,8,8],![7,11,1,1,1,1,1,8,1,8,8,8,8],![10,11,9,8,8,8,8,9,0,0,0,0,0],![10,11,1,1,1,1,1,0,1,7,7,7,7],![10,11,1,1,8,8,8,0,7,1,0,0,0],![9,11,1,1,8,8,8,0,7,0,1,0,0],![10,10,1,1,8,8,8,0,7,0,0,1,0],![10,11,1,8,8,8,8,0,7,0,0,0,1]],![![7,7,7,7,7,7,7,10,10,10,9,10,10],![7,9,11,9,11,11,11,11,11,11,11,12,11],![7,11,1,1,1,1,1,8,1,1,1,1,8],![7,9,1,10,0,0,0,1,0,2,9,2,2],![7,11,1,0,0,0,0,8,0,2,2,2,2],![7,11,1,0,0,0,0,8,0,2,2,2,2],![7,11,1,0,0,0,0,8,0,2,2,2,2],![10,11,8,1,8,8,8,1,0,0,0,0,0],![10,11,1,0,0,0,0,0,0,2,2,2,2],![10,11,1,2,2,2,2,0,2,2,2,2,2],![9,11,1,9,2,2,2,0,2,2,9,2,2],![10,12,1,2,2,2,2,0,2,2,2,2,2],![10,11,8,2,2,2,2,0,2,2,2,2,2]],![![7,7,7,7,7,7,8,8,10,10,9,10,10],![7,9,11,11,9,12,12,12,12,12,12,12,11],![7,11,1,1,1,1,1,8,1,8,8,8,8],![7,11,1,0,0,0,0,8,0,2,2,2,2],![7,9,1,0,8,3,3,1,2,3,3,3,3],![7,12,1,0,3,3,3,3,2,3,3,3,3],![8,12,1,0,3,3,3,3,2,3,3,3,3],![8,12,8,8,1,3,3,1,3,3,3,3,3],![10,12,1,0,2,2,2,3,2,1,1,1,1],![10,12,8,2,3,3,3,3,1,3,3,3,3],![9,12,8,2,3,3,3,3,1,3,3,3,3],![10,12,8,2,3,3,3,3,1,3,3,3,3],![10,11,8,2,3,3,3,3,1,3,3,3,3]],![![7,7,7,7,7,7,7,8,10,10,9,10,10],![7,9,11,11,12,9,12,12,12,12,12,12,11],![7,11,1,1,1,1,1,8,1,8,8,8,8],![7,11,1,0,0,0,0,8,0,2,2,2,2],![7,12,1,0,3,3,3,3,2,3,3,3,3],![7,9,1,0,3,3,4,4,4,4,4,4,4],![7,12,1,0,3,4,4,4,4,4,4,4,4],![8,12,8,8,3,4,4,4,4,4,4,4,4],![10,12,1,0,2,4,4,4,4,4,4,4,4],![10,12,8,2,3,4,4,4,4,4,4,4,4],![9,12,8,2,3,4,4,4,4,4,4,4,4],![10,12,8,2,3,4,4,4,4,4,4,4,4],![10,11,8,2,3,4,4,4,4,4,4,4,4]],![![7,7,7,7,8,7,7,8,10,10,9,10,11],![7,9,11,11,12,12,9,12,12,12,12,12,11],![7,11,1,1,1,1,1,8,1,8,8,8,8],![7,11,1,0,0,0,0,8,0,2,2,2,2],![8,12,1,0,3,3,3,3,2,3,3,3,3],![7,12,1,0,3,4,4,4,4,4,4,4,4],![7,9,1,0,3,4,11,5,5,5,5,5,5],![8,12,8,8,3,4,5,5,5,5,5,5,5],![10,12,1,0,2,4,5,5,5,5,5,5,5],![10,12,8,2,3,4,5,5,5,5,5,5,5],![9,12,8,2,3,4,5,5,5,5,5,5,5],![10,12,8,2,3,4,5,5,5,5,5,5,5],![11,11,8,2,3,4,5,5,5,5,5,5,5]],![![9,9,10,10,8,8,8,9,9,8,8,8,8],![9,9,11,11,12,12,12,9,0,12,12,12,11],![10,11,9,8,8,8,8,9,0,0,0,0,0],![10,11,8,1,8,8,8,1,0,0,0,0,0],![8,12,8,8,1,3,3,1,3,3,3,3,3],![8,12,8,8,3,4,4,4,4,4,4,4,4],![8,12,8,8,3,4,5,5,5,5,5,5,5],![9,9,9,1,1,4,5,4,5,5,5,6,6],![9,0,0,0,3,4,5,5,5,5,5,5,5],![8,12,0,0,3,4,5,5,5,5,6,6,6],![8,12,0,0,3,4,5,5,5,6,5,6,6],![8,12,0,0,3,4,5,6,5,6,6,6,6],![8,11,0,0,3,4,5,6,5,6,6,6,6]],![![9,9,10,10,10,10,10,9,9,7,7,7,7],![9,9,11,11,12,12,12,0,9,12,12,12,11],![10,11,1,1,1,1,1,0,1,7,7,7,7],![10,11,1,0,0,0,0,0,0,2,2,2,2],![10,12,1,0,2,2,2,3,2,1,1,1,1],![10,12,1,0,2,4,4,4,4,4,4,4,4],![10,12,1,0,2,4,5,5,5,5,5,5,5],![9,0,0,0,3,4,5,5,5,5,5,5,5],![9,9,1,0,2,4,5,5,6,6,6,6,6],![7,12,7,2,1,4,5,5,6,6,6,6,6],![7,12,7,2,1,4,5,5,6,6,6,6,6],![7,12,7,2,1,4,5,5,6,6,6,6,6],![7,11,7,2,1,4,5,5,6,6,6,6,6]],![![7,10,10,10,10,10,10,8,7,7,11,10,11],![10,0,11,11,12,12,12,12,12,0,12,12,11],![10,11,1,1,8,8,8,0,7,1,0,0,0],![10,11,1,2,2,2,2,0,2,2,2,2,2],![10,12,8,2,3,3,3,3,1,3,3,3,3],![10,12,8,2,3,4,4,4,4,4,4,4,4],![10,12,8,2,3,4,5,5,5,5,5,5,5],![8,12,0,0,3,4,5,5,5,5,6,6,6],![7,12,7,2,1,4,5,5,6,6,6,6,6],![7,0,1,2,3,4,5,5,6,12,6,6,6],![11,12,0,2,3,4,5,6,6,6,6,6,6],![10,12,0,2,3,4,5,6,6,6,6,6,6],![11,11,0,2,3,4,5,6,6,6,6,6,6]],![![9,9,9,9,9,9,9,8,7,11,9,9,11],![9,9,11,11,12,12,12,12,12,12,9,12,11],![9,11,1,1,8,8,8,0,7,0,1,0,0],![9,11,1,9,2,2,2,0,2,2,9,2,2],![9,12,8,2,3,3,3,3,1,3,3,3,3],![9,12,8,2,3,4,4,4,4,4,4,4,4],![9,12,8,2,3,4,5,5,5,5,5,5,5],![8,12,0,0,3,4,5,5,5,6,5,6,6],![7,12,7,2,1,4,5,5,6,6,6,6,6],![11,12,0,2,3,4,5,6,6,6,6,6,6],![9,9,1,9,3,4,5,5,6,6,1,6,6],![9,12,0,2,3,4,5,6,6,6,6,6,6],![11,11,0,2,3,4,5,6,6,6,6,6,6]],![![9,10,10,10,10,10,10,8,7,10,9,9,10],![10,9,10,12,12,12,12,12,12,12,12,9,10],![10,10,1,1,8,8,8,0,7,0,0,1,0],![10,12,1,2,2,2,2,0,2,2,2,2,2],![10,12,8,2,3,3,3,3,1,3,3,3,3],![10,12,8,2,3,4,4,4,4,4,4,4,4],![10,12,8,2,3,4,5,5,5,5,5,5,5],![8,12,0,0,3,4,5,6,5,6,6,6,6],![7,12,7,2,1,4,5,5,6,6,6,6,6],![10,12,0,2,3,4,5,6,6,6,6,6,6],![9,12,0,2,3,4,5,6,6,6,6,6,6],![9,9,1,2,3,4,5,6,6,6,6,2,6],![10,10,0,2,3,4,5,6,6,6,6,6,6]],![![9,10,10,10,10,10,11,8,7,11,11,10,9],![10,9,11,11,11,11,11,11,11,11,11,10,9],![10,11,1,8,8,8,8,0,7,0,0,0,1],![10,11,8,2,2,2,2,0,2,2,2,2,2],![10,11,8,2,3,3,3,3,1,3,3,3,3],![10,11,8,2,3,4,4,4,4,4,4,4,4],![11,11,8,2,3,4,5,5,5,5,5,5,5],![8,11,0,0,3,4,5,6,5,6,6,6,6],![7,11,7,2,1,4,5,5,6,6,6,6,6],![11,11,0,2,3,4,5,6,6,6,6,6,6],![11,11,0,2,3,4,5,6,6,6,6,6,6],![10,10,0,2,3,4,5,6,6,6,6,6,6],![9,9,1,2,3,4,5,6,6,6,6,6,5]]]

theorem condorcet_acyclic_root_claims : ∀ a b c : Fin 13,
    condorcet_acyclic_root_relation (condorcet_acyclic_root_table a b c) a ∧
    condorcet_acyclic_root_relation (condorcet_acyclic_root_table a b c) b ∧
    condorcet_acyclic_root_relation (condorcet_acyclic_root_table a b c) c := by
  decide

theorem condorcet_acyclic_root_coherent : ∀ a b c : Fin 13,
    condorcet_acyclic_root_table a b c = condorcet_acyclic_root_table b a c ∧
    condorcet_acyclic_root_table a b c = condorcet_acyclic_root_table a c b := by
  decide

theorem condorcet_acyclic_root_duplicates : ∀ a b : Fin 13,
    condorcet_acyclic_root_table a a b = condorcet_acyclic_root_table a b b := by
  decide

theorem condorcet_acyclic_root_uniform : ∀ r : Fin 13,
    (univ.filter fun t : Fin 13 × Fin 13 × Fin 13 =>
      condorcet_acyclic_root_table t.1 t.2.1 t.2.2 = r).card = 169 := by
  decide

theorem condorcet_acyclic_root_chain_wellFounded :
    WellFounded (fun a b : {a : Fin 13 // a.val < 7} =>
      condorcet_acyclic_root_relation a.val b.val) := by
  refine (measure (fun a : {a : Fin 13 // a.val < 7} => a.val.val)).wf.mono ?_
  intro a b hab
  change a.val.val < b.val.val
  rcases hab with ⟨_, ha | hb | h⟩
  · omega
  · omega
  · exact h

theorem condorcet_acyclic_root_core_card (A : Finset (Fin 13))
    (hA : WellFounded (fun a b : {a : Fin 13 // a ∈ A} =>
      condorcet_acyclic_root_relation a.val b.val)) :
    (A.filter fun a => 7 ≤ a.val).card ≤ 1 := by
  classical
  apply card_le_one.mpr
  intro a ha b hb
  have haA := (mem_filter.mp ha).1
  have hbA := (mem_filter.mp hb).1
  by_contra hab
  have hr : condorcet_acyclic_root_relation a b :=
    ⟨hab, Or.inl (mem_filter.mp ha).2⟩
  have hs : condorcet_acyclic_root_relation b a :=
    ⟨Ne.symm hab, Or.inl (mem_filter.mp hb).2⟩
  exact hA.asymmetric (a := ⟨a,haA⟩) (b := ⟨b,hbA⟩) hr hs

theorem condorcet_acyclic_root_weight_bound (A : Finset (Fin 13))
    (hA : WellFounded (fun a b : {a : Fin 13 // a ∈ A} =>
      condorcet_acyclic_root_relation a.val b.val)) :
    2 * (∑ a ∈ A, if 7 ≤ a.val then (1 : ℝ) else 0) <
      ∑ a : Fin 13, if 7 ≤ a.val then (1 : ℝ) else 0 := by
  classical
  have hc := condorcet_acyclic_root_core_card A hA
  have hc' : ((A.filter fun a => 7 ≤ a.val).card : ℝ) ≤ 1 := by exact_mod_cast hc
  have hsum : (∑ a ∈ A, if 7 ≤ a.val then (1 : ℝ) else 0) =
      ((A.filter fun a => 7 ≤ a.val).card : ℝ) := by simp [← sum_filter]
  have hcard : (univ.filter fun a : Fin 13 => 7 ≤ a.val).card = 6 := by decide
  have htotal : (∑ a : Fin 13, if 7 ≤ a.val then (1 : ℝ) else 0) = 6 := by
    have h := congrArg (fun z : ℕ => (z : ℝ)) hcard
    simpa [← sum_filter] using h
  rw [hsum, htotal]
  linarith

theorem condorcet_acyclic_root_no_half_cover
    (n : ℕ) (V : Fin n → Finset (Fin 13)) (hn : 0 < n)
    (hV : ∀ v, WellFounded (fun a b : {a : Fin 13 // a ∈ V v} =>
      condorcet_acyclic_root_relation a.val b.val)) :
    ¬ (∀ a, n ≤ 2 * (univ.filter fun v => a ∈ V v).card) := by
  classical
  intro hhalf
  exact condorcet_half_cover_finite_weighted_half_cover_exclusion 13 n hn V hhalf
    (fun a => if 7 ≤ a.val then (1 : ℝ) else 0)
    (fun a => by split_ifs <;> positivity)
    (fun v => condorcet_acyclic_root_weight_bound _ (hV v))

theorem condorcet_product_fixed_point_acyclic_mass_obstruction :
    ∃ (R : Fin 13 → Fin 13 → Prop)
      (f : Fin 13 → Fin 13 → Fin 13 → Fin 13) (U : Finset (Fin 13)),
      (∀ a, ¬ R a a) ∧
      (∀ a b c, R (f a b c) a ∧ R (f a b c) b ∧ R (f a b c) c) ∧
      (∀ a b c, f a b c = f b a c ∧ f a b c = f a c b) ∧
      (∀ a b, f a a b = f a b b) ∧
      (∀ r, (univ.filter fun t : Fin 13 × Fin 13 × Fin 13 =>
        f t.1 t.2.1 t.2.2 = r).card = 169) ∧
      U.card = 7 ∧
      WellFounded (fun a b : {a : Fin 13 // a ∈ U} => R a.val b.val) ∧
      (∀ (n : ℕ) (V : Fin n → Finset (Fin 13)), 0 < n →
        (∀ v, WellFounded (fun a b : {a : Fin 13 // a ∈ V v} => R a.val b.val)) →
        ¬ (∀ a, n ≤ 2 * (univ.filter fun v => a ∈ V v).card)) := by
  let U : Finset (Fin 13) := univ.filter fun a => a.val < 7
  refine ⟨condorcet_acyclic_root_relation, condorcet_acyclic_root_table, U,
    ?_, condorcet_acyclic_root_claims, condorcet_acyclic_root_coherent,
    condorcet_acyclic_root_duplicates, condorcet_acyclic_root_uniform, ?_, ?_,
    condorcet_acyclic_root_no_half_cover⟩
  · intro a
    simp [condorcet_acyclic_root_relation]
  · decide
  · let g : {a : Fin 13 // a ∈ U} → {a : Fin 13 // a.val < 7} :=
      fun a => ⟨a.val, (mem_filter.mp a.property).2⟩
    exact InvImage.wf g condorcet_acyclic_root_chain_wellFounded
