import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet

/-!
# condorcet_acyclic_half_cover_of_no_winning_k

Topic: social_choice   Node: 4009d50eddf0

Provenance: helper lemma. IN-383, OP-19 campaign session 9, 2026-10-30. Structural verification of the maximum-potential neighborhood route suggested in IN-380. Generalization of the existing acyclic-cover reduction, whose strict election definition is from Condorcet winning sets, Social Choice and Welfare 44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . No new election bound or research novelty is claimed.

For any n and k, a finite n-voter election with no strict Condorcet winning set of size at most k yields a finite relation with outside common predecessors for all sets of at most k vertices and an acyclic half-cover with the same n voters.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_acyclic_half_cover_of_no_winning_k
    (n m k : ℕ) (P : Fin n → Equiv.Perm (Fin m))
    (hfail : ∀ S : Finset (Fin m), S.card ≤ k → ¬is_condorcet_winning_set P S) :
    ∃ (q : ℕ) (R : Fin q → Fin q → Prop) (U : Fin n → Finset (Fin q)),
      (∀ J : Finset (Fin q), J.card ≤ k → ∃ a,a∉J ∧ ∀ b∈J,R a b) ∧
      (∀ v,WellFounded (fun a b : {a : Fin q // a∈U v} => R a.val b.val)) ∧
      (∀ a,n≤2*(univ.filter fun v => a∈U v).card) := by
  classical
  let I := {T : Finset (Fin m) // T.card≤k}
  let q := Fintype.card I
  let e : I ≃ Fin q := Fintype.equivFin I
  let S : Fin q → Finset (Fin m) := fun i => (e.symm i).val
  have hchoose : ∀ i : Fin q,∃ a,a∉S i ∧
      n≤2*(univ.filter fun v => ∀ c∈S i,P v a < P v c).card := by
    intro i
    have h := hfail (S i) (e.symm i).property
    unfold is_condorcet_winning_set at h
    push_neg at h
    exact h
  choose f hfout hfcount using hchoose
  let R : Fin q → Fin q → Prop := fun i j => f j∈S i
  let U : Fin n → Finset (Fin q) := fun v =>
    univ.filter fun i => ∀ c∈S i,P v (f i) < P v c
  refine ⟨q,R,U,?_,?_,?_⟩
  · intro J hJ
    let T := J.image f
    have hT : T.card≤k := (card_image_le).trans hJ
    let i := e ⟨T,hT⟩
    have hi : S i=T := by simp [S,i]
    refine ⟨i,?_,?_⟩
    · intro hiJ
      apply hfout i
      rw [hi]
      exact mem_image.mpr ⟨i,hiJ,rfl⟩
    · intro j hj
      change f j∈S i
      rw [hi]
      exact mem_image.mpr ⟨j,hj,rfl⟩
  · intro v
    refine (measure (fun a : {a : Fin q // a∈U v} => (P v (f a.val)).val)).wf.mono ?_
    intro a b hab
    have hactive := (mem_filter.mp a.property).2
    exact hactive (f b.val) hab
  · intro a
    simpa only [U,mem_filter,mem_univ,true_and] using hfcount a
