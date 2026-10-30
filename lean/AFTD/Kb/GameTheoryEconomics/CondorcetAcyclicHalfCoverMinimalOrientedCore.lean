import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetDimensionLeThreeIffOrientedAcyclicWeightSeparation
import AFTD.Kb.GameTheoryEconomics.CondorcetTriplePredecessorArcMinimal
import AFTD.Kb.GameTheoryEconomics.CondorcetReversalTensorAcyclicHalfCoverIff

/-!
# condorcet_acyclic_half_cover_minimal_oriented_core

Topic: social_choice   Node: c7e91fb21cdb

Provenance: helper lemma. IN-362 structural counterexample reduction for OP-19. Combines the already verified oriented tensor lift with ordinary minimum-counterexample and finite arc-minimization arguments. No new election bound or research advance.

Any integer acyclic half-cover of an S3 relation on m vertices yields a half-cover with the same number of voters on k vertices, where4<=k<=19*m. The new relation is oriented, its only induced S3 subset is the entire graph, and each arrow belongs to a private triple of exactly three vertices. Thus a hypothetical election counterexample may be assumed to satisfy all three restrictions simultaneously. The factor19 comes from an explicit oriented tensor lift; there is no absolute upper bound on k, and no half-cover is asserted to exist.
-/

open Finset
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_oriented_half_cover_restrict
    (m n : ℕ) (R : Fin m → Fin m → Prop) (U : Fin n → Finset (Fin m))
    (hR : ∀ a b, R a b → ¬ R b a)
    (B : Finset (Fin m))
    (hB : ∀ J : Finset (Fin m), J ⊆ B → J.card ≤ 3 →
      ∃ a, a ∈ B ∧ a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hhalf : ∀ a, n ≤ 2 * (univ.filter fun v => a ∈ U v).card) :
    ∃ (Q : Fin B.card → Fin B.card → Prop) (V : Fin n → Finset (Fin B.card)),
      (∀ a b, Q a b → ¬ Q b a) ∧
      (∀ J : Finset (Fin B.card), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, Q a b) ∧
      (∀ v, WellFounded (fun a b : {a : Fin B.card // a ∈ V v} => Q a.val b.val)) ∧
      (∀ a, n ≤ 2 * (univ.filter fun v => a ∈ V v).card) := by
  classical
  let e : {a : Fin m // a ∈ B} ≃ Fin B.card := Fintype.equivFinOfCardEq (Fintype.card_coe B)
  let liftVertex : Fin B.card → Fin m := fun a => (e.symm a).val
  let Q : Fin B.card → Fin B.card → Prop := fun a b => R (liftVertex a) (liftVertex b)
  obtain ⟨V,hV,hcount⟩ := condorcet_tensor_half_cover_pullback Q R liftVertex
    (fun a b hab => hab) n U hU
  refine ⟨Q,V,?_,?_,hV,?_⟩
  · intro a b hab hba
    exact hR (liftVertex a) (liftVertex b) hab hba
  · intro J hJ
    have hsub : J.image liftVertex ⊆ B := by
      intro a ha
      obtain ⟨b,_,rfl⟩ := mem_image.mp ha
      exact (e.symm b).property
    obtain ⟨a,haB,haJ,haR⟩ := hB (J.image liftVertex) hsub (card_image_le.trans hJ)
    let a' : Fin B.card := e ⟨a,haB⟩
    have hlift : liftVertex a' = a := by simp [liftVertex,a']
    refine ⟨a',?_,?_⟩
    · intro ha'
      exact haJ (mem_image.mpr ⟨a',ha',hlift⟩)
    · intro b hb
      change R (liftVertex a') (liftVertex b)
      rw [hlift]
      exact haR (liftVertex b) (mem_image.mpr ⟨b,hb,rfl⟩)
  · intro a
    rw [hcount a]
    exact hhalf (liftVertex a)

theorem condorcet_oriented_half_cover_choose_minimum
    (m n : ℕ) (R : Fin m → Fin m → Prop) (U : Fin n → Finset (Fin m))
    (hR : ∀ a b, R a b → ¬ R b a)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hhalf : ∀ a, n ≤ 2 * (univ.filter fun v => a ∈ U v).card) :
    ∃ (k : ℕ) (Q : Fin k → Fin k → Prop) (V : Fin n → Finset (Fin k)),
      4 ≤ k ∧ k ≤ m ∧
      (∀ a b, Q a b → ¬ Q b a) ∧
      (∀ J : Finset (Fin k), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, Q a b) ∧
      (∀ B : Finset (Fin k),
        (∀ J : Finset (Fin k), J ⊆ B → J.card ≤ 3 →
          ∃ a, a ∈ B ∧ a ∉ J ∧ ∀ b ∈ J, Q a b) → B = univ) ∧
      (∀ a b, Q a b → ∃ J : Finset (Fin k), J.card = 3 ∧ b ∈ J ∧ a ∉ J ∧
        (∀ c ∈ J, Q a c) ∧ ∀ d, d ∉ J → (∀ c ∈ J, Q d c) → d = a) ∧
      (∀ v, WellFounded (fun a b : {a : Fin k // a ∈ V v} => Q a.val b.val)) ∧
      (∀ a, n ≤ 2 * (univ.filter fun v => a ∈ V v).card) := by
  classical
  let P : ℕ → Prop := fun k => ∃ (T : Fin k → Fin k → Prop) (W : Fin n → Finset (Fin k)),
    (∀ a b, T a b → ¬ T b a) ∧
    (∀ J : Finset (Fin k), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, T a b) ∧
    (∀ v, WellFounded (fun a b : {a : Fin k // a ∈ W v} => T a.val b.val)) ∧
    (∀ a, n ≤ 2 * (univ.filter fun v => a ∈ W v).card)
  have hex : ∃ k, P k := ⟨m,R,U,hR,hroot,hU,hhalf⟩
  let k := Nat.find hex
  obtain ⟨T,W,hT,hTroot,hW,hWhalf⟩ : P k := Nat.find_spec hex
  obtain ⟨Q,hQT,_,hQroot,hprivate⟩ := condorcet_triple_predecessor_arc_minimal k T hTroot
  have hQ : ∀ a b, Q a b → ¬ Q b a := by
    intro a b hab hba
    exact hT a b (hQT a b hab) (hQT b a hba)
  have hWQ : ∀ v, WellFounded (fun a b : {a : Fin k // a ∈ W v} => Q a.val b.val) := by
    intro v
    exact (hW v).mono (fun a b hab => hQT a.val b.val hab)
  have hfour : 4 ≤ k := by
    by_contra h
    have hsmall : (univ : Finset (Fin k)).card ≤ 3 := by simpa using (show k ≤ 3 by omega)
    obtain ⟨a,ha,_⟩ := hQroot univ hsmall
    exact ha (mem_univ a)
  refine ⟨k,Q,W,hfour,?_,hQ,hQroot,?_,hprivate,hWQ,hWhalf⟩
  · exact Nat.find_min' hex ⟨R,U,hR,hroot,hU,hhalf⟩
  · intro B hB
    have hPB : P B.card := condorcet_oriented_half_cover_restrict k n Q W hQ B hB hWQ hWhalf
    have hle : k ≤ B.card := Nat.find_min' hex hPB
    apply eq_of_subset_of_card_le (subset_univ B)
    simpa only [card_univ,Fintype.card_fin] using hle

theorem condorcet_acyclic_half_cover_minimal_oriented_core
    (m n : ℕ) (R : Fin m → Fin m → Prop) (U : Fin n → Finset (Fin m))
    (hroot : ∀ J : Finset (Fin m), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hhalf : ∀ a, n ≤ 2 * (univ.filter fun v => a ∈ U v).card) :
    ∃ (k : ℕ) (Q : Fin k → Fin k → Prop) (V : Fin n → Finset (Fin k)),
      4 ≤ k ∧ k ≤ m * 19 ∧
      (∀ a b, Q a b → ¬ Q b a) ∧
      (∀ J : Finset (Fin k), J.card ≤ 3 → ∃ a, a ∉ J ∧ ∀ b ∈ J, Q a b) ∧
      (∀ B : Finset (Fin k),
        (∀ J : Finset (Fin k), J ⊆ B → J.card ≤ 3 →
          ∃ a, a ∈ B ∧ a ∉ J ∧ ∀ b ∈ J, Q a b) → B = univ) ∧
      (∀ a b, Q a b → ∃ J : Finset (Fin k), J.card = 3 ∧ b ∈ J ∧ a ∉ J ∧
        (∀ c ∈ J, Q a c) ∧ ∀ d, d ∉ J → (∀ c ∈ J, Q d c) → d = a) ∧
      (∀ v, WellFounded (fun a b : {a : Fin k // a ∈ V v} => Q a.val b.val)) ∧
      (∀ a, n ≤ 2 * (univ.filter fun v => a ∈ V v).card) := by
  obtain ⟨T,W,hT,hTroot,hW,hWhalf⟩ := condorcet_oriented_tensor_half_cover_lift m n R U hroot hU hhalf
  exact condorcet_oriented_half_cover_choose_minimum (m * 19) n T W hT hTroot hW hWhalf
