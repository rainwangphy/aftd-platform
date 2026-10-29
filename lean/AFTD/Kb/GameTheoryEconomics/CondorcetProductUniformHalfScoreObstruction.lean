import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.F

/-!
# condorcet_product_uniform_half_score_obstruction

Topic: social_choice   Node: 35a40d77b2c4

Provenance: helper lemma. IN-348 diagnostic helper for OP-19. Related published product fixed-point construction: https://theorydish.blog/2026/09/11/condorcet-quintets-a-proof-from-the-book/ and https://arxiv.org/html/2609.35186v1 section 3. The construction uses one translation-equivariant root per orbit of nonempty subsets of size at most three in the 23-candidate quadratic-residue tournament; all finite identities are checked by the Lean kernel. The general election theorem, optimized marginal certificates, and other possible fixed points remain unresolved. No research advance is claimed.

There is a strict regular tournament on 23 candidates, every candidate beating exactly 11 others, and a root map for ordered triples. Each root beats all three sampled candidates. The map is invariant under input permutations and identifying the two multiplicity patterns of a two-candidate sample. Every candidate is the root of exactly 529 ordered triples, so uniform iid sampling has uniform root output. Nevertheless the identity ranking satisfies exactly 6148 of the 12167 ordered root-versus-sample claims, strictly more than half. This is a limitation of a pointwise product-fixed-point proof step, not an election in which every three-candidate committee fails.
-/

open Finset
open scoped BigOperators
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def condorcet_product_uniform_product_table : Fin 23 → Fin 23 → Fin 23 :=
  ![![22,22,22,22,21,22,21,22,22,20,21,22,11,11,11,14,15,15,17,17,19,20,21],
    ![22,22,22,22,21,22,21,22,22,20,21,22,11,11,11,11,15,15,15,15,11,20,21],
    ![22,22,22,22,21,22,21,22,22,19,21,22,22,7,21,22,7,22,17,17,19,19,21],
    ![22,22,22,22,14,22,20,22,22,20,20,22,22,10,10,14,14,14,17,17,17,20,20],
    ![21,21,21,14,21,19,21,21,19,19,21,21,11,11,11,14,15,15,15,15,19,19,21],
    ![22,22,22,22,19,22,20,22,22,20,20,22,22,20,10,22,15,15,15,15,19,20,20],
    ![21,21,21,20,21,20,21,21,5,20,21,21,11,20,21,11,21,5,17,17,17,20,21],
    ![22,22,22,22,21,22,21,22,22,14,21,22,22,5,21,14,14,14,17,17,17,17,21],
    ![22,22,22,22,19,22,5,22,22,19,7,22,22,7,19,22,7,15,15,7,19,19,19],
    ![20,20,19,20,19,20,20,14,19,20,20,7,19,20,19,7,7,5,5,7,19,20,20],
    ![21,21,21,20,21,20,21,21,7,20,21,21,17,20,21,7,7,15,17,7,7,20,21],
    ![22,22,22,22,21,22,21,22,22,7,21,22,22,10,10,22,10,22,10,10,7,5,10],
    ![11,11,22,22,11,22,11,22,22,19,17,22,11,11,11,11,10,11,10,11,11,19,10],
    ![11,11,7,10,11,20,20,5,7,20,20,10,11,11,11,11,10,11,10,11,11,20,10],
    ![11,11,21,10,11,10,21,21,19,19,21,10,11,11,11,11,10,11,10,11,11,5,10],
    ![14,11,22,14,14,22,11,14,22,7,7,22,11,11,11,14,14,14,14,11,14,20,14],
    ![15,15,7,14,15,15,21,14,7,7,7,10,10,10,10,14,15,15,15,15,14,15,14],
    ![15,15,22,14,15,15,5,14,15,5,15,22,11,11,11,14,15,15,15,15,14,15,14],
    ![17,15,17,17,15,15,17,17,15,5,17,10,10,10,10,14,15,15,17,17,17,17,14],
    ![17,15,17,17,15,15,17,17,7,7,7,10,11,11,11,11,15,15,17,17,17,17,10],
    ![19,11,19,17,19,19,17,17,19,19,7,7,11,11,11,14,14,14,17,17,19,19,19],
    ![20,20,19,20,19,20,20,17,19,20,20,5,19,20,5,20,15,15,17,17,19,20,20],
    ![21,21,21,20,21,20,21,21,19,20,21,10,10,10,10,14,14,14,14,10,19,20,21]]



def condorcet_product_uniform_fast_root (a b c : Fin 23) : Fin 23 :=
  a + condorcet_product_uniform_product_table (b-a) (c-a)

def condorcet_product_uniform_fast_equiv : (Fin 23 × Fin 23 × Fin 23) ≃
    (Fin 23 × Fin 23 × Fin 23) where
  toFun t := (t.2.1-t.1,t.2.2-t.1,condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2)
  invFun t :=
    let a := t.2.2-condorcet_product_uniform_product_table t.1 t.2.1
    (a,a+t.1,a+t.2.1)
  left_inv t := by
    rcases t with ⟨a,b,c⟩
    simp [condorcet_product_uniform_fast_root]
  right_inv t := by
    rcases t with ⟨d,e,r⟩
    simp [condorcet_product_uniform_fast_root]

def condorcet_product_uniform_fast_fiber (r : Fin 23) :
    {t : Fin 23 × Fin 23 × Fin 23 // condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2=r} ≃
      Fin 23 × Fin 23 where
  toFun t := (t.val.2.1-t.val.1,t.val.2.2-t.val.1)
  invFun t := ⟨condorcet_product_uniform_fast_equiv.symm (t.1,t.2,r),by
    have h := congrArg (fun t => t.2.2) (condorcet_product_uniform_fast_equiv.apply_symm_apply (t.1,t.2,r))
    exact h⟩
  left_inv t := by
    apply Subtype.ext
    apply condorcet_product_uniform_fast_equiv.injective
    rw [condorcet_product_uniform_fast_equiv.apply_symm_apply]
    exact Prod.ext rfl (Prod.ext rfl t.property.symm)
  right_inv t := by
    have h := condorcet_product_uniform_fast_equiv.apply_symm_apply (t.1,t.2,r)
    exact congrArg (fun t => (t.1,t.2.1)) h

theorem condorcet_product_uniform_fast_uniform : ∀ r : Fin 23,
    (univ.filter fun t : Fin 23 × Fin 23 × Fin 23 =>
      condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 = r).card = 529 := by
  intro r
  rw [← Fintype.card_subtype, Fintype.card_congr (condorcet_product_uniform_fast_fiber r)]
  decide

theorem condorcet_product_uniform_fast_mod_lt (r d : Fin 23) :
    r < r-d ↔ r.val < d.val := by
  rw [Fin.lt_def, Fin.sub_def]
  change r.val < (23-d.val+r.val)%23 ↔ r.val < d.val
  omega

def condorcet_product_uniform_fast_cut (d e : Fin 23) : ℕ :=
  min (condorcet_product_uniform_product_table d e).val
    (min ((condorcet_product_uniform_product_table d e)-d).val ((condorcet_product_uniform_product_table d e)-e).val)

theorem condorcet_product_uniform_fast_cut_le (d e : Fin 23) : condorcet_product_uniform_fast_cut d e < 23 := by
  exact lt_of_le_of_lt (min_le_left _ _) (condorcet_product_uniform_product_table d e).isLt

theorem condorcet_product_uniform_fast_score_iff (d e r : Fin 23) :
    let t := condorcet_product_uniform_fast_equiv.symm (d,e,r)
    (condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 < t.1 ∧
      condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 < t.2.1 ∧
      condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 < t.2.2) ↔ r.val < condorcet_product_uniform_fast_cut d e := by
  dsimp only [condorcet_product_uniform_fast_equiv, Equiv.coe_fn_symm_mk]
  simp only [condorcet_product_uniform_fast_root, add_sub_cancel_left, sub_add_cancel]
  have h₁ : r-condorcet_product_uniform_product_table d e+d = r-(condorcet_product_uniform_product_table d e-d) := by abel
  have h₂ : r-condorcet_product_uniform_product_table d e+e = r-(condorcet_product_uniform_product_table d e-e) := by abel
  rw [h₁,h₂]
  simp only [condorcet_product_uniform_fast_mod_lt,condorcet_product_uniform_fast_cut,lt_min_iff]

theorem condorcet_product_uniform_fast_count_lt (d e : Fin 23) :
    (∑ r : Fin 23, if r.val < condorcet_product_uniform_fast_cut d e then 1 else 0) =
      condorcet_product_uniform_fast_cut d e := by
  let c : Fin 23 := ⟨condorcet_product_uniform_fast_cut d e,condorcet_product_uniform_fast_cut_le d e⟩
  have hset : (univ.filter fun r : Fin 23 => r.val < condorcet_product_uniform_fast_cut d e) = Iio c := by
    ext r
    simp [c,Fin.lt_def]
  rw [← Finset.sum_filter]
  simp only [sum_const, smul_eq_mul, mul_one, hset, Fin.card_Iio]
  rfl

theorem condorcet_product_uniform_fast_cut_sum : (∑ d : Fin 23, ∑ e : Fin 23, condorcet_product_uniform_fast_cut d e) = 6148 := by
  decide

theorem condorcet_product_uniform_fast_score :
    (univ.filter fun t : Fin 23 × Fin 23 × Fin 23 =>
      condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 < t.1 ∧
      condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 < t.2.1 ∧
      condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 < t.2.2).card = 6148 := by
  let F : (Fin 23 × Fin 23 × Fin 23) → ℕ := fun t =>
    if condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 < t.1 ∧
      condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 < t.2.1 ∧
      condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 < t.2.2 then 1 else 0
  have hc : (univ.filter fun t : Fin 23 × Fin 23 × Fin 23 =>
      condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 < t.1 ∧
      condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 < t.2.1 ∧
      condorcet_product_uniform_fast_root t.1 t.2.1 t.2.2 < t.2.2).card = ∑ t,F t := by
    simp [F, ← Finset.sum_filter]
  rw [hc]
  calc
    (∑ t,F t) = ∑ t,F (condorcet_product_uniform_fast_equiv.symm t) :=
      (Equiv.sum_comp condorcet_product_uniform_fast_equiv.symm F).symm
    _ = ∑ d : Fin 23, ∑ e : Fin 23, ∑ r : Fin 23,
        if r.val < condorcet_product_uniform_fast_cut d e then 1 else 0 := by
      simp only [Fintype.sum_prod_type]
      apply sum_congr rfl
      intro d hd
      apply sum_congr rfl
      intro e he
      apply sum_congr rfl
      intro r hr
      simp only [F,condorcet_product_uniform_fast_score_iff]
    _ = 6148 := by simp_rw [condorcet_product_uniform_fast_count_lt]; exact condorcet_product_uniform_fast_cut_sum


-- Append to ProductFast.lean. Only small relative-coordinate censuses
-- remain; the full product counting is structural.
def condorcet_product_uniform_fast_rel (a b : Fin 23) : Prop :=
  (b-a).val ∈ ([1,2,3,4,6,8,9,12,13,16,18] : List ℕ)

instance : DecidableRel condorcet_product_uniform_fast_rel := fun _ _ =>
  inferInstanceAs (Decidable (_ ∈ (_ : List ℕ)))

theorem condorcet_product_uniform_fast_tournament :
    (∀ a, ¬ condorcet_product_uniform_fast_rel a a) ∧
    (∀ a b, condorcet_product_uniform_fast_rel a b → ¬ condorcet_product_uniform_fast_rel b a) ∧
    (∀ a b, a ≠ b → condorcet_product_uniform_fast_rel a b ∨ condorcet_product_uniform_fast_rel b a) := by decide

theorem condorcet_product_uniform_fast_regular : ∀ a : Fin 23,
    (univ.filter fun b => condorcet_product_uniform_fast_rel a b).card = 11 := by decide

theorem condorcet_product_uniform_fast_local : ∀ d e,
    condorcet_product_uniform_fast_rel (condorcet_product_uniform_product_table d e) 0 ∧
    condorcet_product_uniform_fast_rel (condorcet_product_uniform_product_table d e) d ∧
    condorcet_product_uniform_fast_rel (condorcet_product_uniform_product_table d e) e := by decide

theorem condorcet_product_uniform_fast_table_swap : ∀ d e,
    condorcet_product_uniform_product_table d e = condorcet_product_uniform_product_table e d := by decide

theorem condorcet_product_uniform_fast_table_shift : ∀ d e,
    condorcet_product_uniform_product_table d e = d + condorcet_product_uniform_product_table (-d) (e-d) := by decide

theorem condorcet_product_uniform_fast_table_duplicate : ∀ d,
    condorcet_product_uniform_product_table 0 d = condorcet_product_uniform_product_table d d := by decide

theorem condorcet_product_uniform_fast_compatible : ∀ a b c,
    condorcet_product_uniform_fast_rel (condorcet_product_uniform_fast_root a b c) a ∧
    condorcet_product_uniform_fast_rel (condorcet_product_uniform_fast_root a b c) b ∧
    condorcet_product_uniform_fast_rel (condorcet_product_uniform_fast_root a b c) c := by
  intro a b c
  have h := condorcet_product_uniform_fast_local (b-a) (c-a)
  have shift (x y t : Fin 23) : condorcet_product_uniform_fast_rel (x+t) (y+t) ↔ condorcet_product_uniform_fast_rel x y := by
    simp only [condorcet_product_uniform_fast_rel,add_sub_add_right_eq_sub]
  refine ⟨?_,?_,?_⟩
  · simpa only [zero_add,add_comm (condorcet_product_uniform_product_table (b-a) (c-a)) a,condorcet_product_uniform_fast_root] using
      (shift (condorcet_product_uniform_product_table (b-a) (c-a)) 0 a).mpr h.1
  · simpa only [sub_add_cancel,add_comm (condorcet_product_uniform_product_table (b-a) (c-a)) a,condorcet_product_uniform_fast_root] using
      (shift (condorcet_product_uniform_product_table (b-a) (c-a)) (b-a) a).mpr h.2.1
  · simpa only [sub_add_cancel,add_comm (condorcet_product_uniform_product_table (b-a) (c-a)) a,condorcet_product_uniform_fast_root] using
      (shift (condorcet_product_uniform_product_table (b-a) (c-a)) (c-a) a).mpr h.2.2

theorem condorcet_product_uniform_fast_symmetric : ∀ a b c,
    condorcet_product_uniform_fast_root a b c = condorcet_product_uniform_fast_root b a c ∧
    condorcet_product_uniform_fast_root a b c = condorcet_product_uniform_fast_root a c b := by
  intro a b c
  constructor
  · have h₁ : -(b-a) = a-b := by abel
    have h₂ : (c-a)-(b-a) = c-b := by abel
    dsimp only [condorcet_product_uniform_fast_root]
    rw [condorcet_product_uniform_fast_table_shift (b-a) (c-a),h₁,h₂]
    abel
  · dsimp only [condorcet_product_uniform_fast_root]
    rw [condorcet_product_uniform_fast_table_swap (b-a) (c-a)]

theorem condorcet_product_uniform_fast_duplicate : ∀ a b,
    condorcet_product_uniform_fast_root a a b = condorcet_product_uniform_fast_root a b b := by
  intro a b
  simp only [condorcet_product_uniform_fast_root,sub_self,condorcet_product_uniform_fast_table_duplicate]

theorem condorcet_product_uniform_half_score_obstruction :
    ∃ (R : Fin 23 → Fin 23 → Prop) (f : Fin 23 → Fin 23 → Fin 23 → Fin 23),
      (∀ a, ¬ R a a) ∧
      (∀ a b, R a b → ¬ R b a) ∧
      (∀ a b, a ≠ b → R a b ∨ R b a) ∧
      (∀ a, Nat.card {b : Fin 23 // R a b} = 11) ∧
      (∀ a b c, R (f a b c) a ∧ R (f a b c) b ∧ R (f a b c) c) ∧
      (∀ a b c, f a b c = f b a c ∧ f a b c = f a c b) ∧
      (∀ a b, f a a b = f a b b) ∧
      (∀ r : Fin 23,
        (Finset.univ.filter fun t : Fin 23 × Fin 23 × Fin 23 =>
          f t.1 t.2.1 t.2.2 = r).card = 529) ∧
      (Finset.univ.filter fun t : Fin 23 × Fin 23 × Fin 23 =>
        f t.1 t.2.1 t.2.2 < t.1 ∧ f t.1 t.2.1 t.2.2 < t.2.1 ∧
        f t.1 t.2.1 t.2.2 < t.2.2).card = 6148 := by
  classical
  refine ⟨condorcet_product_uniform_fast_rel,
    condorcet_product_uniform_fast_root,
    condorcet_product_uniform_fast_tournament.1,
    condorcet_product_uniform_fast_tournament.2.1,
    condorcet_product_uniform_fast_tournament.2.2, ?_,
    condorcet_product_uniform_fast_compatible,
    condorcet_product_uniform_fast_symmetric,
    condorcet_product_uniform_fast_duplicate,
    condorcet_product_uniform_fast_uniform,
    condorcet_product_uniform_fast_score⟩
  intro a
  simpa [Nat.card_eq_fintype_card, Fintype.card_subtype] using
    condorcet_product_uniform_fast_regular a
