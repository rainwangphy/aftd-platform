import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetCommonPredecessorNeighborhood

/-!
# condorcet_potential_maximum_neighborhood_half_cover

Topic: social_choice   Node: 16dfcd821328

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural verification of the maximum-potential neighborhood route suggested in IN-380. Generalization of the existing acyclic-cover reduction, whose strict election definition is from Condorcet winning sets, Social Choice and Welfare 44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . No new election bound or research novelty is claimed.

Suppose a finite relation has outside common predecessors for every set of at most k+1 vertices. If n induced acyclic sets and a real potential satisfy n+h(b) <= 2*coverage(a)+h(a) on every arrow a to b, then some finite relation with the k-predecessor property has an acyclic half-cover with the same n sets. The new relation is obtained by restricting to the predecessors of a maximum-potential vertex.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_potential_maximum_neighborhood_half_cover
    (m n k : ℕ) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m)) (h : Fin m → ℝ)
    (hroot : ∀ J : Finset (Fin m), J.card ≤ k+1 →
      ∃ a, a ∉ J ∧ ∀ b ∈ J, R a b)
    (hU : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hlocal : ∀ a b, R a b →
      (n : ℝ)+h b ≤ 2*((univ.filter fun v => a∈U v).card : ℝ)+h a) :
    ∃ (q : ℕ) (Q : Fin q → Fin q → Prop) (W : Fin n → Finset (Fin q)),
      (∀ J : Finset (Fin q), J.card ≤ k →
        ∃ a, a ∉ J ∧ ∀ b ∈ J, Q a b) ∧
      (∀ v, WellFounded (fun a b : {a : Fin q // a ∈ W v} => Q a.val b.val)) ∧
      (∀ a, n ≤ 2*(univ.filter fun v => a∈W v).card) := by
  classical
  obtain ⟨r,_,_⟩ := hroot ∅ (by simp)
  obtain ⟨b,_,hb⟩ := exists_max_image univ h ⟨r,mem_univ _⟩
  let D := {a : Fin m // R a b}
  let q := Fintype.card D
  let e : D ≃ Fin q := Fintype.equivFin D
  let Q : Fin q → Fin q → Prop := fun a c => R (e.symm a).val (e.symm c).val
  let W : Fin n → Finset (Fin q) := fun v => univ.filter (fun a => (e.symm a).val ∈ U v)
  refine ⟨q,Q,W,?_,?_,?_⟩
  · intro J hJ
    have hJ' : (J.image e.symm).card ≤ k := card_image_le.trans hJ
    obtain ⟨a,ha,har⟩ := condorcet_common_predecessor_neighborhood R k hroot b
      (J.image e.symm) hJ'
    refine ⟨e a,?_,?_⟩
    · intro hmem
      exact ha (mem_image.mpr ⟨e a,hmem,e.symm_apply_apply a⟩)
    · intro c hc
      change R (e.symm (e a)).val (e.symm c).val
      rw [e.symm_apply_apply]
      exact har _ (mem_image.mpr ⟨c,hc,rfl⟩)
  · intro v
    let f : {a : Fin q // a ∈ W v} → {a : Fin m // a∈U v} :=
      fun a => ⟨(e.symm a.val).val,(mem_filter.mp a.property).2⟩
    exact InvImage.wf f (hU v)
  · intro a
    have hle := hlocal (e.symm a).val b (e.symm a).property
    have hmax := hb (e.symm a).val (mem_univ _)
    have hc : (n : ℝ) ≤ 2*((univ.filter fun v => (e.symm a).val ∈ U v).card : ℝ) := by
      linarith
    have heq : (univ.filter fun v => a ∈ W v) =
        (univ.filter fun v => (e.symm a).val ∈ U v) := by simp [W]
    rw [heq]
    exact_mod_cast hc
