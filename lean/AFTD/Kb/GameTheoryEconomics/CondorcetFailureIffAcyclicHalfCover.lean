import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsCondorcetWinningSet
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.Support
import AFTD.Kb.GameTheoryEconomics.PiLexFinite

/-!
# condorcet_failure_iff_acyclic_half_cover

Topic: social_choice   Node: 2e7b22ff65a6

Provenance: helper lemma. IN-348 structural reformulation helper for OP-19, with the unchanged strict definition in Condorcet winning sets, Social Choice and Welfare44(3):493-517 (2015), https://www.lamsade.dauphine.fr/~lang/papers/els15.pdf . Related acyclic-cover framework: https://arxiv.org/abs/2609.35186 and https://arxiv.org/abs/2610.29043 . Large-girth common-predecessor examples appear in Theorem11 of https://drops.dagstuhl.de/storage/00lipics/lipics-vol040-approx-random2015/LIPIcs.APPROX-RANDOM.2015.78/LIPIcs.APPROX-RANDOM.2015.78.pdf ; their existence is not assumed or formalized by this helper. No claim of novelty or research advance. An earlier informal fixed-witness acyclic-cover research proposal is recorded at https://www.proofatlas.ai/collaboration/condorcet-winning-sets-equality-overthrow/ (checked2026-10-29). That unaudited route map does not supply the Lean proof or an election theorem; the present helper is not claimed as a novel research result.

Fix a positive number n of voters. There exists a finite election with these n voters in which every candidate set of size at most three fails to be a strict Condorcet winning set if and only if there exist a finite directed relation R and n vertex subsets U, one per voter, with three properties: every set J of at most three graph vertices has an outside vertex related by R to all members of J; R restricted to each U is acyclic; and every graph vertex belongs to at least half of the n subsets. The graph vertex count may differ from the original election candidate count. On finite types acyclicity is expressed by WellFounded of the restricted relation. This is an equivalent reformulation and supplies no graph witness or new dimension bound.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

-- High-girth common-predecessor constructions from the literature show
-- why a uniform bounded-support certificate cannot be assumed. This file
-- proves the local finite implication; it does not formalize that existence
-- construction or claim a new election bound.

theorem condorcet_acyclic_cover_wellFounded_sources {A : Type*} (R : A → A → Prop)
    (U : Set A)
    (h : WellFounded (fun a b : U => R a.val b.val)) :
    WellFounded (fun a b : A => a ∈ U ∧ R a b) := by
  have hroot : ∀ u : U, Acc (fun a b : A => a ∈ U ∧ R a b) u.val := by
    intro u
    induction u using h.induction with
    | h u ih =>
      apply Acc.intro
      intro a ha
      exact ih ⟨a,ha.1⟩ ha.2
  constructor
  intro a
  apply Acc.intro
  intro b hb
  exact hroot ⟨b,hb.1⟩

structure condorcet_acyclic_cover_order_vertex (m : ℕ) where
  val : Fin m
deriving Fintype

def condorcet_acyclic_cover_order_vertex_equiv (m : ℕ) : condorcet_acyclic_cover_order_vertex m ≃ Fin m where
  toFun := condorcet_acyclic_cover_order_vertex.val
  invFun := condorcet_acyclic_cover_order_vertex.mk
  left_inv _ := rfl
  right_inv _ := rfl

theorem condorcet_acyclic_cover_ranking_of_wellFounded (m : ℕ) (R : Fin m → Fin m → Prop)
    (hR : WellFounded R) :
    ∃ σ : Equiv.Perm (Fin m), ∀ a b, R a b → σ a < σ b := by
  classical
  let A := condorcet_acyclic_cover_order_vertex m
  let r : A → A → Prop := fun a b => R a.val b.val
  letI : IsWellFounded A r := ⟨InvImage.wf condorcet_acyclic_cover_order_vertex.val hR⟩
  let ord : LinearOrder A := IsWellFounded.wellOrderExtension r
  letI : LinearOrder A := ord
  have hcard : Fintype.card A = m := by
    exact (Fintype.card_congr (condorcet_acyclic_cover_order_vertex_equiv m)).trans (Fintype.card_fin m)
  let e := (@Fintype.orderIsoFinOfCardEq A ord inferInstance m hcard).symm
  let σ : Equiv.Perm (Fin m) :=
    { toFun := fun a => e ⟨a⟩
      invFun := fun a => (e.symm a).val
      left_inv := by intro a; simp
      right_inv := by
        intro a
        change e (condorcet_acyclic_cover_order_vertex.mk (e.symm a).val) = a
        have h : condorcet_acyclic_cover_order_vertex.mk (e.symm a).val = e.symm a := by
          cases e.symm a
          rfl
        rw [h]
        exact e.apply_symm_apply a }
  refine ⟨σ,?_⟩
  intro a b hab
  apply e.strictMono
  have hab' : r (condorcet_acyclic_cover_order_vertex.mk a) (condorcet_acyclic_cover_order_vertex.mk b) := hab
  exact Prod.Lex.left _ _ (IsWellFounded.rank_lt_of_rel (r := r) hab')

theorem condorcet_acyclic_cover_ordering_certificate_needs_cyclic_root_support
    (m q : ℕ) (S : Fin q → Finset (Fin m))
    (f : Fin q → Fin m) (w : Fin q → ℕ)
    (R : Fin m → Fin m → Prop)
    (hcomp : ∀ i, ∀ c ∈ S i, R (f i) c)
    (hacyclic : WellFounded (fun a b :
      {a : Fin m // ∃ i, w i ≠ 0 ∧ f i = a} => R a.val b.val)) :
    ∃ σ : Equiv.Perm (Fin m),
      (∑ i, if ∀ c ∈ S i, σ (f i) < σ c then w i else 0) = ∑ i,w i := by
  classical
  let U : Set (Fin m) := {a | ∃ i,w i ≠ 0 ∧ f i=a}
  obtain ⟨σ,hσ⟩ := condorcet_acyclic_cover_ranking_of_wellFounded m
    (fun a b => a∈U ∧ R a b) (condorcet_acyclic_cover_wellFounded_sources R U hacyclic)
  refine ⟨σ, Finset.sum_congr rfl ?_⟩
  intro i hi
  by_cases hw : w i = 0
  · simp [hw]
  · have hgood : ∀ c ∈ S i, σ (f i) < σ c := by
      intro c hc
      exact hσ (f i) c ⟨⟨i,hw,rfl⟩,hcomp i c hc⟩
    exact if_pos hgood


theorem condorcet_acyclic_cover_no_winning_three_of_acyclic_half_cover
    (n m : ℕ) (hn : 0 < n) (R : Fin m → Fin m → Prop)
    (U : Fin n → Finset (Fin m))
    (hroot : ∀ S : Finset (Fin m), S.card ≤ 3 →
      ∃ a, a ∉ S ∧ ∀ c ∈ S,R a c)
    (hacyclic : ∀ v, WellFounded (fun a b : {a : Fin m // a ∈ U v} => R a.val b.val))
    (hhalf : ∀ a, n ≤ 2*(univ.filter fun v => a∈U v).card) :
    ∃ P : Fin n → Equiv.Perm (Fin m),
      ∀ S : Finset (Fin m), S.card ≤ 3 → ¬ is_condorcet_winning_set P S := by
  classical
  have horders : ∀ v, ∃ σ : Equiv.Perm (Fin m),
      ∀ a b, a∈U v → R a b → σ a < σ b := by
    intro v
    obtain ⟨σ,hσ⟩ := condorcet_acyclic_cover_ranking_of_wellFounded m
      (fun a b => a∈U v ∧ R a b)
      (condorcet_acyclic_cover_wellFounded_sources R {a | a∈U v} (hacyclic v))
    exact ⟨σ,fun a b ha hab => hσ a b ⟨ha,hab⟩⟩
  choose P hP using horders
  refine ⟨P,?_⟩
  intro S hS hwin
  obtain ⟨a,ha,hdom⟩ := hroot S hS
  have hsub : (univ.filter fun v => a∈U v) ⊆
      (univ.filter fun v => ∀ c∈S,P v a < P v c) := by
    intro v hv
    refine mem_filter.mpr ⟨mem_univ v,?_⟩
    intro c hc
    exact hP v a c (mem_filter.mp hv).2 (hdom c hc)
  have hb := (hhalf a).trans (Nat.mul_le_mul_left 2 (card_le_card hsub))
  exact (not_lt_of_ge hb) (hwin a ha)


theorem condorcet_acyclic_cover_acyclic_half_cover_of_no_winning_three
    (n m : ℕ) (_hn : 0 < n) (P : Fin n → Equiv.Perm (Fin m))
    (hfail : ∀ S : Finset (Fin m), S.card ≤ 3 → ¬is_condorcet_winning_set P S) :
    ∃ (q : ℕ) (R : Fin q → Fin q → Prop) (U : Fin n → Finset (Fin q)),
      (∀ J : Finset (Fin q), J.card ≤ 3 → ∃ a,a∉J ∧ ∀ b∈J,R a b) ∧
      (∀ v,WellFounded (fun a b : {a : Fin q // a∈U v} => R a.val b.val)) ∧
      (∀ a,n≤2*(univ.filter fun v => a∈U v).card) := by
  classical
  let I := {T : Finset (Fin m) // T.card≤3}
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
    have hT : T.card≤3 := (card_image_le).trans hJ
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

theorem condorcet_failure_iff_acyclic_half_cover (n : ℕ) (hn : 0 < n) :
    (∃ (m : ℕ) (P : Fin n → Equiv.Perm (Fin m)),
      ∀ S : Finset (Fin m),S.card≤3 → ¬is_condorcet_winning_set P S) ↔
    (∃ (q : ℕ) (R : Fin q → Fin q → Prop) (U : Fin n → Finset (Fin q)),
      (∀ J : Finset (Fin q),J.card≤3 → ∃ a,a∉J ∧ ∀ b∈J,R a b) ∧
      (∀ v,WellFounded (fun a b : {a : Fin q // a∈U v} => R a.val b.val)) ∧
      (∀ a,n≤2*(univ.filter fun v => a∈U v).card)) := by
  constructor
  · rintro ⟨m,P,hP⟩
    exact condorcet_acyclic_cover_acyclic_half_cover_of_no_winning_three n m hn P hP
  · rintro ⟨q,R,U,hroot,hacyclic,hhalf⟩
    obtain ⟨P,hP⟩ := condorcet_acyclic_cover_no_winning_three_of_acyclic_half_cover n q hn R U hroot hacyclic hhalf
    exact ⟨q,P,hP⟩
