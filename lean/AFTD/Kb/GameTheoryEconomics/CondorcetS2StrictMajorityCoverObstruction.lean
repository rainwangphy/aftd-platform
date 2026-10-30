import AFTD.Prelude

/-!
# condorcet_s2_strict_majority_cover_obstruction

Topic: social_choice   Node: 6dd8fe9872d8

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural analysis of the S2-to-S3 completion route from IN-362; finite diagnostics audited in experiments9630 and9640. Supports the general campaign only; no new election bound or research novelty is claimed.

An explicit eighteen-vertex relation has outside common predecessors for every set of at most two vertices and has nine induced acyclic sets covering each vertex exactly five times. It explicitly fails the corresponding three-vertex predecessor property. Thus S2 and strict majority coverage alone do not yield a contradiction; this does not refute the special three-of-five auxiliary.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 30000000
set_option maxRecDepth 20000

theorem condorcet_s2_strict_majority_cover_obstruction :
    ∃ (R : Fin 18 → Fin 18 → Prop) (U : Fin 9 → Finset (Fin 18)),
      (∀ J : Finset (Fin 18), J.card ≤ 2 →
        ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) ∧
      (∀ v, WellFounded (fun a b : {a : Fin 18 // a ∈ U v} => R a.val b.val)) ∧
      (∀ a, (univ.filter fun v => a∈U v).card = 5) ∧
      ¬(∀ J : Finset (Fin 18), J.card ≤ 3 →
        ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b) := by
  let R : Fin 18 → Fin 18 → Prop := fun a b =>
    (a.val / 6 = b.val / 6 ∧ b.val % 6 = (a.val % 6 + 1) % 6) ∨
      b.val / 6 = (a.val / 6 + 1) % 3
  letI (a b : Fin 18) : Decidable (R a b) := inferInstanceAs (Decidable
    ((a.val / 6 = b.val / 6 ∧ b.val % 6 = (a.val % 6 + 1) % 6) ∨
      b.val / 6 = (a.val / 6 + 1) % 3))
  let U : Fin 9 → Finset (Fin 18) := ![{7,8,9,10,11,13,14,15,16,17},
    {6,8,9,10,11,12,14,15,16,17},
    {6,7,9,10,11,12,13,15,16,17},
    {1,2,3,4,5,12,13,14,16,17},
    {0,2,3,4,5,12,13,14,15,17},
    {0,1,3,4,5,12,13,14,15,16},
    {0,1,2,4,5,6,7,8,10,11},
    {0,1,2,3,5,6,7,8,9,11},
    {0,1,2,3,4,6,7,8,9,10}]
  let ord : Fin 9 → Fin 18 → ℕ := ![![0,0,0,0,0,0,0,0,1,2,3,4,0,5,6,7,8,9],
    ![0,0,0,0,0,0,4,0,0,1,2,3,9,0,5,6,7,8],
    ![0,0,0,0,0,0,3,4,0,0,1,2,8,9,0,5,6,7],
    ![0,5,6,7,8,9,0,0,0,0,0,0,2,3,4,0,0,1],
    ![9,0,5,6,7,8,0,0,0,0,0,0,1,2,3,4,0,0],
    ![8,9,0,5,6,7,0,0,0,0,0,0,0,1,2,3,4,0],
    ![2,3,4,0,0,1,7,8,9,0,5,6,0,0,0,0,0,0],
    ![1,2,3,4,0,0,6,7,8,9,0,5,0,0,0,0,0,0],
    ![0,1,2,3,4,0,5,6,7,8,9,0,0,0,0,0,0,0]]
  have hloop : ∀ a, ¬ R a a := by decide
  have hpair : ∀ a b, ∃ c, R c a ∧ R c b := by decide
  have hroot : ∀ J : Finset (Fin 18), J.card ≤ 2 →
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
          simpa only [mem_singleton.mp hb] using hca
      · have h2 : J.card = 2 := by omega
        obtain ⟨a,b,hab,rfl⟩ := card_eq_two.mp h2
        obtain ⟨c,hca,hcb⟩ := hpair a b
        refine ⟨c,?_,?_⟩
        · simp only [mem_insert,mem_singleton,not_or]
          exact ⟨fun heq => hloop a (heq ▸ hca),fun heq => hloop b (heq ▸ hcb)⟩
        · intro d hd
          simp only [mem_insert,mem_singleton] at hd
          rcases hd with rfl|rfl
          · exact hca
          · exact hcb
  have horder : ∀ v a b, a∈U v → b∈U v → R a b → ord v a < ord v b := by decide
  have hU : ∀ v, WellFounded (fun a b : {a : Fin 18 // a ∈ U v} => R a.val b.val) := by
    intro v
    refine (measure (fun a : {a : Fin 18 // a ∈ U v} => ord v a.val)).wf.mono ?_
    intro a b hab
    exact horder v a b a.property b.property hab
  have hcover : ∀ a, (univ.filter fun v => a∈U v).card = 5 := by decide
  refine ⟨R,U,hroot,hU,hcover,?_⟩
  intro hthree
  obtain ⟨a,_,ha⟩ := hthree {0,6,12} (by decide)
  have hbad : ∀ a, ¬(R a 0 ∧ R a 6 ∧ R a 12) := by decide
  exact hbad a ⟨ha 0 (by simp),ha 6 (by simp),ha 12 (by simp)⟩
