import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetProductUniformHalfScoreObstruction

/-!
# condorcet_uniform_distinct_three_half_score_obstruction

Topic: social_choice   Node: 23700be8f485

Provenance: helper lemma. IN-348 method diagnostic for OP-19. Builds on the Lean-proved23-candidate construction condorcet_product_uniform_half_score_obstruction, using five clones per candidate and the three-input affine mean in the clone group. Related published product fixed-point route: https://theorydish.blog/2026/09/11/condorcet-quintets-a-proof-from-the-book/ . The root is symmetric and therefore defines a selector on three-element sets. No assertion about duplicate-sample coherence of this Lean root is needed for this distinct-triple statement; the separately audited full set-mean extension in experiment8690 is not this theorem. This result obstructs only fixed raw uniform weights, not general balanced weights, all possible fixed points, or OP-19. No research advance is claimed.

On the 115 candidates represented as a base candidate in Fin23 and a clone in Fin5, there is a strict regular tournament, each candidate beating57 others, and a root map invariant under input permutations and beating all three sampled candidates in that tournament. Among ordered triples of pairwise distinct candidates, every root has exactly12882 preimages. There is a bijective ranking in which exactly741420 of the1481430 distinct ordered triple claims are satisfied, strictly more than half. Thus raw uniform weights for distinct three-candidate committees need not provide a pointwise half-score certificate, even with uniform root marginals and tournament compatibility. No election defeating every committee and no impossibility of selector-adapted weights is asserted.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

def condorcet_distinct_certificate_relative_root {G : Type*} [AddCommGroup G] (g : G → G → G) (a b c : G) :=
  a+g (b-a) (c-a)

def condorcet_distinct_certificate_relative_equiv {G : Type*} [AddCommGroup G] (g : G → G → G) :
    (G × G × G) ≃ (G × G × G) where
  toFun t := (t.2.1-t.1,t.2.2-t.1,condorcet_distinct_certificate_relative_root g t.1 t.2.1 t.2.2)
  invFun t := let a := t.2.2-g t.1 t.2.1; (a,a+t.1,a+t.2.1)
  left_inv t := by rcases t with ⟨a,b,c⟩; simp [condorcet_distinct_certificate_relative_root]
  right_inv t := by rcases t with ⟨d,e,r⟩; simp [condorcet_distinct_certificate_relative_root]

def condorcet_distinct_certificate_distinct {G : Type*} (t : G × G × G) : Prop :=
  t.1≠t.2.1 ∧ t.1≠t.2.2 ∧ t.2.1≠t.2.2

instance {G : Type*} [DecidableEq G] : DecidablePred (@condorcet_distinct_certificate_distinct G) := fun _ =>
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

theorem condorcet_distinct_certificate_distinct_iff {G : Type*} [AddCommGroup G] (a b c : G) :
    condorcet_distinct_certificate_distinct (a,b,c) ↔ (b-a)≠0 ∧ (c-a)≠0 ∧ (b-a)≠(c-a) := by
  constructor
  · rintro ⟨hab,hac,hbc⟩
    refine ⟨sub_ne_zero.mpr hab.symm,sub_ne_zero.mpr hac.symm,?_⟩
    intro h
    apply hbc
    simpa using congrArg (fun x => x+a) h
  · rintro ⟨hd,he,hde⟩
    refine ⟨(sub_ne_zero.mp hd).symm,(sub_ne_zero.mp he).symm,?_⟩
    intro h
    exact hde (congrArg (fun x => x-a) h)

def condorcet_distinct_certificate_distinct_fiber_equiv {G : Type*} [AddCommGroup G]
    (g : G → G → G) (r : G) :
    {t : G × G × G // condorcet_distinct_certificate_distinct t ∧ condorcet_distinct_certificate_relative_root g t.1 t.2.1 t.2.2=r} ≃
      {u : G × G // u.1≠0 ∧ u.2≠0 ∧ u.1≠u.2} where
  toFun t := ⟨(t.val.2.1-t.val.1,t.val.2.2-t.val.1),
    (condorcet_distinct_certificate_distinct_iff _ _ _).mp t.property.1⟩
  invFun u := ⟨(condorcet_distinct_certificate_relative_equiv g).symm (u.val.1,u.val.2,r),by
    have he := (condorcet_distinct_certificate_relative_equiv g).apply_symm_apply (u.val.1,u.val.2,r)
    constructor
    · apply (condorcet_distinct_certificate_distinct_iff _ _ _).mpr
      simpa only [condorcet_distinct_certificate_relative_equiv,Equiv.coe_fn_symm_mk,add_sub_cancel_left] using u.property
    · exact congrArg (fun t => t.2.2) he⟩
  left_inv t := by
    apply Subtype.ext
    apply (condorcet_distinct_certificate_relative_equiv g).injective
    rw [Equiv.apply_symm_apply]
    exact Prod.ext rfl (Prod.ext rfl t.property.2.symm)
  right_inv u := by
    apply Subtype.ext
    exact congrArg (fun t => (t.1,t.2.1))
      ((condorcet_distinct_certificate_relative_equiv g).apply_symm_apply (u.val.1,u.val.2,r))

theorem condorcet_distinct_certificate_distinct_uniform {G : Type*} [AddCommGroup G]
    [Fintype G] [DecidableEq G] (g : G → G → G) (r : G) :
    (univ.filter fun t : G × G × G => condorcet_distinct_certificate_distinct t ∧
      condorcet_distinct_certificate_relative_root g t.1 t.2.1 t.2.2=r).card =
      ((univ.erase (0 : G)).offDiag).card := by
  rw [← Fintype.card_subtype,Fintype.card_congr (condorcet_distinct_certificate_distinct_fiber_equiv g r),
    Fintype.card_subtype]
  congr 1
  ext u
  simp [Finset.mem_offDiag,ne_comm,and_assoc]

abbrev condorcet_distinct_certificate_group := Fin 23 × Fin 5

def condorcet_distinct_certificate_distinct_table (d e : condorcet_distinct_certificate_group) : condorcet_distinct_certificate_group :=
  (condorcet_product_uniform_product_table d.1 e.1,2*(d.2+e.2))

abbrev condorcet_distinct_certificate_distinct_root := condorcet_distinct_certificate_relative_root condorcet_distinct_certificate_distinct_table

def condorcet_distinct_certificate_distinct_rank (a : condorcet_distinct_certificate_group) : ℕ := 5*a.1.val+a.2.val

theorem condorcet_distinct_certificate_distinct_uniform_concrete : ∀ r : condorcet_distinct_certificate_group,
    (univ.filter fun t : condorcet_distinct_certificate_group × condorcet_distinct_certificate_group × condorcet_distinct_certificate_group =>
      condorcet_distinct_certificate_distinct t ∧ condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2=r).card=12882 := by
  intro r
  rw [condorcet_distinct_certificate_distinct_uniform,Finset.offDiag_card]
  norm_num

theorem condorcet_distinct_certificate_distinct_base (a b c : condorcet_distinct_certificate_group) :
    (condorcet_distinct_certificate_distinct_root a b c).1 =
      condorcet_product_uniform_fast_root a.1 b.1 c.1 := rfl

theorem condorcet_distinct_certificate_distinct_rank_lt (x y : condorcet_distinct_certificate_group) (hne : x.1≠y.1) :
    condorcet_distinct_certificate_distinct_rank x < condorcet_distinct_certificate_distinct_rank y ↔ x.1<y.1 := by
  have hx := x.2.isLt
  have hy := y.2.isLt
  have hval : x.1.val≠y.1.val := fun h => hne (Fin.ext h)
  change 5*x.1.val+x.2.val < 5*y.1.val+y.2.val ↔ x.1.val<y.1.val
  omega

theorem condorcet_distinct_certificate_distinct_root_ne (a b c : condorcet_distinct_certificate_group) :
    (condorcet_distinct_certificate_distinct_root a b c).1≠a.1 ∧
    (condorcet_distinct_certificate_distinct_root a b c).1≠b.1 ∧
    (condorcet_distinct_certificate_distinct_root a b c).1≠c.1 := by
  rw [condorcet_distinct_certificate_distinct_base]
  have h := condorcet_product_uniform_fast_compatible a.1 b.1 c.1
  have hi := condorcet_product_uniform_fast_tournament.1
  constructor
  · intro he
    have hh := h.1
    rw [he] at hh
    exact hi a.1 hh
  constructor
  · intro he
    have hh := h.2.1
    rw [he] at hh
    exact hi b.1 hh
  · intro he
    have hh := h.2.2
    rw [he] at hh
    exact hi c.1 hh

theorem condorcet_distinct_certificate_distinct_score_coordinates (d e r : condorcet_distinct_certificate_group) :
    let t := (condorcet_distinct_certificate_relative_equiv condorcet_distinct_certificate_distinct_table).symm (d,e,r)
    (condorcet_distinct_certificate_distinct_rank (condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2) < condorcet_distinct_certificate_distinct_rank t.1 ∧
      condorcet_distinct_certificate_distinct_rank (condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2) < condorcet_distinct_certificate_distinct_rank t.2.1 ∧
      condorcet_distinct_certificate_distinct_rank (condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2) < condorcet_distinct_certificate_distinct_rank t.2.2) ↔
      r.1.val < condorcet_product_uniform_fast_cut d.1 e.1 := by
  dsimp only
  let t := (condorcet_distinct_certificate_relative_equiv condorcet_distinct_certificate_distinct_table).symm (d,e,r)
  have hn := condorcet_distinct_certificate_distinct_root_ne t.1 t.2.1 t.2.2
  rw [condorcet_distinct_certificate_distinct_rank_lt _ _ hn.1,condorcet_distinct_certificate_distinct_rank_lt _ _ hn.2.1,
      condorcet_distinct_certificate_distinct_rank_lt _ _ hn.2.2]
  exact condorcet_product_uniform_fast_score_iff d.1 e.1 r.1

def condorcet_distinct_certificate_distinct_clone_count (d e : Fin 23) : ℕ :=
  (univ.filter fun u : Fin 5 × Fin 5 =>
    (d,u.1)≠(0,0) ∧ (e,u.2)≠(0,0) ∧ (d,u.1)≠(e,u.2)).card

theorem condorcet_distinct_certificate_distinct_weighted_sum :
    (∑ d : Fin 23,∑ e : Fin 23,
      5*condorcet_product_uniform_fast_cut d e*condorcet_distinct_certificate_distinct_clone_count d e)=741420 := by decide

theorem condorcet_distinct_certificate_distinct_coordinates {G : Type*} [AddCommGroup G]
    (g : G → G → G) (d e r : G) :
    condorcet_distinct_certificate_distinct ((condorcet_distinct_certificate_relative_equiv g).symm (d,e,r)) ↔
      d≠0 ∧ e≠0 ∧ d≠e := by
  rw [condorcet_distinct_certificate_distinct_iff]
  simp [condorcet_distinct_certificate_relative_equiv]

theorem condorcet_distinct_certificate_distinct_root_sum (d e : condorcet_distinct_certificate_group) :
    (∑ r : condorcet_distinct_certificate_group,if (d≠0 ∧ e≠0 ∧ d≠e) ∧
      r.1.val < condorcet_product_uniform_fast_cut d.1 e.1 then 1 else 0) =
      if d≠0 ∧ e≠0 ∧ d≠e then 5*condorcet_product_uniform_fast_cut d.1 e.1 else 0 := by
  by_cases h : d≠0 ∧ e≠0 ∧ d≠e
  · rw [if_pos h]
    have hh : (∑ r : condorcet_distinct_certificate_group,if (d≠0 ∧ e≠0 ∧ d≠e) ∧
        r.1.val < condorcet_product_uniform_fast_cut d.1 e.1 then 1 else 0) =
        ∑ a : Fin 23,5*(if a.val < condorcet_product_uniform_fast_cut d.1 e.1 then 1 else 0) := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro a ha
      by_cases hc : a.val < condorcet_product_uniform_fast_cut d.1 e.1
      · simp [h,hc]
      · simp [h,hc]
    rw [hh,← Finset.mul_sum,condorcet_product_uniform_fast_count_lt]
  · simp [h]

theorem condorcet_distinct_certificate_distinct_pair_sum (d e : Fin 23) :
    (∑ x : Fin 5,∑ y : Fin 5,
      if (d,x)≠(0,0) ∧ (e,y)≠(0,0) ∧ (d,x)≠(e,y)
        then 5*condorcet_product_uniform_fast_cut d e else 0) =
      5*condorcet_product_uniform_fast_cut d e*condorcet_distinct_certificate_distinct_clone_count d e := by
  have hc : condorcet_distinct_certificate_distinct_clone_count d e =
      ∑ u : Fin 5 × Fin 5,
        if (d,u.1)≠(0,0) ∧ (e,u.2)≠(0,0) ∧ (d,u.1)≠(e,u.2) then 1 else 0 := by
    unfold condorcet_distinct_certificate_distinct_clone_count
    rw [card_eq_sum_ones,sum_filter]
  rw [hc]
  simp only [Fintype.sum_prod_type,mul_sum,mul_ite,mul_one,mul_zero]

theorem condorcet_distinct_certificate_distinct_score :
    (univ.filter fun t : condorcet_distinct_certificate_group × condorcet_distinct_certificate_group × condorcet_distinct_certificate_group =>
      condorcet_distinct_certificate_distinct t ∧
      condorcet_distinct_certificate_distinct_rank (condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2) < condorcet_distinct_certificate_distinct_rank t.1 ∧
      condorcet_distinct_certificate_distinct_rank (condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2) < condorcet_distinct_certificate_distinct_rank t.2.1 ∧
      condorcet_distinct_certificate_distinct_rank (condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2) < condorcet_distinct_certificate_distinct_rank t.2.2).card=741420 := by
  let P : (condorcet_distinct_certificate_group × condorcet_distinct_certificate_group × condorcet_distinct_certificate_group) → ℕ := fun t =>
    if condorcet_distinct_certificate_distinct t ∧
      condorcet_distinct_certificate_distinct_rank (condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2) < condorcet_distinct_certificate_distinct_rank t.1 ∧
      condorcet_distinct_certificate_distinct_rank (condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2) < condorcet_distinct_certificate_distinct_rank t.2.1 ∧
      condorcet_distinct_certificate_distinct_rank (condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2) < condorcet_distinct_certificate_distinct_rank t.2.2 then 1 else 0
  have hc : (univ.filter fun t : condorcet_distinct_certificate_group × condorcet_distinct_certificate_group × condorcet_distinct_certificate_group =>
      condorcet_distinct_certificate_distinct t ∧
      condorcet_distinct_certificate_distinct_rank (condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2) < condorcet_distinct_certificate_distinct_rank t.1 ∧
      condorcet_distinct_certificate_distinct_rank (condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2) < condorcet_distinct_certificate_distinct_rank t.2.1 ∧
      condorcet_distinct_certificate_distinct_rank (condorcet_distinct_certificate_distinct_root t.1 t.2.1 t.2.2) < condorcet_distinct_certificate_distinct_rank t.2.2).card = ∑ t,P t := by
    rw [card_eq_sum_ones,sum_filter]
  rw [hc]
  calc
    (∑ t,P t) = ∑ t,P ((condorcet_distinct_certificate_relative_equiv condorcet_distinct_certificate_distinct_table).symm t) :=
      (Equiv.sum_comp (condorcet_distinct_certificate_relative_equiv condorcet_distinct_certificate_distinct_table).symm P).symm
    _ = ∑ d : condorcet_distinct_certificate_group,∑ e : condorcet_distinct_certificate_group,∑ r : condorcet_distinct_certificate_group,
        if (d≠0 ∧ e≠0 ∧ d≠e) ∧ r.1.val < condorcet_product_uniform_fast_cut d.1 e.1
          then 1 else 0 := by
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro d hd
      rw [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro e he
      apply sum_congr rfl
      intro r hr
      simp only [P,condorcet_distinct_certificate_distinct_coordinates,condorcet_distinct_certificate_distinct_score_coordinates]
    _ = ∑ d : condorcet_distinct_certificate_group,∑ e : condorcet_distinct_certificate_group,
        if d≠0 ∧ e≠0 ∧ d≠e then 5*condorcet_product_uniform_fast_cut d.1 e.1 else 0 := by
      simp_rw [condorcet_distinct_certificate_distinct_root_sum]
    _ = ∑ d : Fin 23,∑ x : Fin 5,∑ e : Fin 23,∑ y : Fin 5,
        if (d,x)≠(0,0) ∧ (e,y)≠(0,0) ∧ (d,x)≠(e,y)
          then 5*condorcet_product_uniform_fast_cut d e else 0 := by
      simp only [Fintype.sum_prod_type]
      rfl
    _ = ∑ d : Fin 23,∑ e : Fin 23,∑ x : Fin 5,∑ y : Fin 5,
        if (d,x)≠(0,0) ∧ (e,y)≠(0,0) ∧ (d,x)≠(e,y)
          then 5*condorcet_product_uniform_fast_cut d e else 0 := by
      apply sum_congr rfl
      intro d hd
      rw [sum_comm]
    _ = 741420 := by
      simp_rw [condorcet_distinct_certificate_distinct_pair_sum]
      exact condorcet_distinct_certificate_distinct_weighted_sum


theorem condorcet_distinct_certificate_distinct_clone_formula (a b c : condorcet_distinct_certificate_group) :
    (condorcet_distinct_certificate_distinct_root a b c).2 = 2*(a.2+b.2+c.2) := by
  have h : ∀ u v w : Fin 5,u+2*((v-u)+(w-u))=2*(u+v+w) := by decide
  exact h a.2 b.2 c.2

theorem condorcet_distinct_certificate_distinct_symmetric : ∀ a b c : condorcet_distinct_certificate_group,
    condorcet_distinct_certificate_distinct_root a b c=condorcet_distinct_certificate_distinct_root b a c ∧
    condorcet_distinct_certificate_distinct_root a b c=condorcet_distinct_certificate_distinct_root a c b := by
  intro a b c
  constructor
  · apply Prod.ext
    · exact (condorcet_product_uniform_fast_symmetric a.1 b.1 c.1).1
    · rw [condorcet_distinct_certificate_distinct_clone_formula,condorcet_distinct_certificate_distinct_clone_formula]
      exact congrArg (fun x : Fin 5 => 2*x) (by abel)
  · apply Prod.ext
    · exact (condorcet_product_uniform_fast_symmetric a.1 b.1 c.1).2
    · rw [condorcet_distinct_certificate_distinct_clone_formula,condorcet_distinct_certificate_distinct_clone_formula]
      exact congrArg (fun x : Fin 5 => 2*x) (by abel)

def condorcet_distinct_certificate_distinct_rel (a b : condorcet_distinct_certificate_group) : Prop :=
  condorcet_product_uniform_fast_rel a.1 b.1 ∨
    (a.1=b.1 ∧ ((b.2-a.2).val=1 ∨ (b.2-a.2).val=2))

instance : DecidableRel condorcet_distinct_certificate_distinct_rel := fun _ _ =>
  inferInstanceAs (Decidable (_ ∨ _))

theorem condorcet_distinct_certificate_distinct_tournament :
    (∀ a : condorcet_distinct_certificate_group,¬condorcet_distinct_certificate_distinct_rel a a) ∧
    (∀ a b,condorcet_distinct_certificate_distinct_rel a b → ¬condorcet_distinct_certificate_distinct_rel b a) ∧
    (∀ a b,a≠b → condorcet_distinct_certificate_distinct_rel a b ∨ condorcet_distinct_certificate_distinct_rel b a) := by decide

theorem condorcet_distinct_certificate_distinct_regular : ∀ a : condorcet_distinct_certificate_group,
    (univ.filter fun b => condorcet_distinct_certificate_distinct_rel a b).card=57 := by decide

theorem condorcet_distinct_certificate_distinct_compatible : ∀ a b c : condorcet_distinct_certificate_group,
    condorcet_distinct_certificate_distinct_rel (condorcet_distinct_certificate_distinct_root a b c) a ∧
    condorcet_distinct_certificate_distinct_rel (condorcet_distinct_certificate_distinct_root a b c) b ∧
    condorcet_distinct_certificate_distinct_rel (condorcet_distinct_certificate_distinct_root a b c) c := by
  intro a b c
  have h := condorcet_product_uniform_fast_compatible a.1 b.1 c.1
  exact ⟨Or.inl h.1,Or.inl h.2.1,Or.inl h.2.2⟩

theorem condorcet_uniform_distinct_three_half_score_obstruction :
    ∃ (R : condorcet_distinct_certificate_group → condorcet_distinct_certificate_group → Prop)
      (f : condorcet_distinct_certificate_group → condorcet_distinct_certificate_group → condorcet_distinct_certificate_group → condorcet_distinct_certificate_group)
      (σ : condorcet_distinct_certificate_group ≃ Fin 115),
      (∀ a,¬R a a) ∧
      (∀ a b,R a b → ¬R b a) ∧
      (∀ a b,a≠b → R a b ∨ R b a) ∧
      (∀ a,Nat.card {b : condorcet_distinct_certificate_group // R a b}=57) ∧
      (∀ a b c,R (f a b c) a ∧ R (f a b c) b ∧ R (f a b c) c) ∧
      (∀ a b c,f a b c=f b a c ∧ f a b c=f a c b) ∧
      (∀ r : condorcet_distinct_certificate_group,
        (univ.filter fun t : condorcet_distinct_certificate_group × condorcet_distinct_certificate_group × condorcet_distinct_certificate_group =>
          condorcet_distinct_certificate_distinct t ∧ f t.1 t.2.1 t.2.2=r).card=12882) ∧
      (univ.filter fun t : condorcet_distinct_certificate_group × condorcet_distinct_certificate_group × condorcet_distinct_certificate_group =>
        condorcet_distinct_certificate_distinct t ∧ σ (f t.1 t.2.1 t.2.2) < σ t.1 ∧
        σ (f t.1 t.2.1 t.2.2) < σ t.2.1 ∧ σ (f t.1 t.2.1 t.2.2) < σ t.2.2).card=741420 := by
  classical
  refine ⟨condorcet_distinct_certificate_distinct_rel,condorcet_distinct_certificate_distinct_root,finProdFinEquiv,
    condorcet_distinct_certificate_distinct_tournament.1,condorcet_distinct_certificate_distinct_tournament.2.1,
    condorcet_distinct_certificate_distinct_tournament.2.2,?_,condorcet_distinct_certificate_distinct_compatible,
    condorcet_distinct_certificate_distinct_symmetric,condorcet_distinct_certificate_distinct_uniform_concrete,?_⟩
  · intro a
    simpa [Nat.card_eq_fintype_card,Fintype.card_subtype] using condorcet_distinct_certificate_distinct_regular a
  · have hrank : ∀ x : condorcet_distinct_certificate_group,
        (finProdFinEquiv x).val=condorcet_distinct_certificate_distinct_rank x := by
      intro x
      change x.2.val+5*x.1.val=5*x.1.val+x.2.val
      omega
    simpa only [Fin.lt_def,hrank] using condorcet_distinct_certificate_distinct_score
