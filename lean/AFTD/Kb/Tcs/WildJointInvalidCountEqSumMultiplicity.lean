import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointInvalidCount
import AFTD.Kb.Tcs.WildJointMultiplicity
import AFTD.Kb.Tcs.WildJointBlockSet
import AFTD.Kb.Tcs.WildJointBlock

/-!
# wild_joint_invalid_count_eq_sum_multiplicity

Topic: graphs   Node: 95d376c69852

Provenance: helper lemma. step towards wild_one_bad_color_mixed_moment_formula_with_context

For every vertex permutation σ, the invalid-colour count I(σ) equals the sum, over the q blocks, of the witness-support multiplicity mu of that block.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option linter.unusedSimpArgs false
open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000

lemma wild_array_support_eq_three_iff {n : ℕ}
    (a b c z : Fin n) (hab : a ≠ b) (hac : a ≠ c) (hbc : b ≠ c)
    (hza : z ≠ a) (hzb : z ≠ b) :
    ({a,b,z} : Finset (Fin n)) = {a,b,c} ↔ z = c := by
  constructor
  · intro h
    have hc : c ∈ ({a,b,z} : Finset (Fin n)) := by rw [h]; simp
    exact (by simpa [Ne.symm hac,Ne.symm hbc] using hc : c=z).symm
  · rintro rfl; rfl

lemma wild_joint_multiplicity_eq_invalid_colors
    (q : ℕ) (A : Fin (3*q) → Fin (3*q) → Fin (3*q))
    (hid : ∀ a,A a a=a) (hsym : ∀ a b,A a b=A b a)
    (hinj : ∀ a,Function.Injective (A a))
    (T : Finset (Fin (3*q))) (hT : T.card=3) :
    wild_joint_multiplicity q A T =
      (T.filter fun i => ∃ x∈T,∃ y∈T,x≠y ∧ A x y=i).card := by
  classical
  obtain ⟨a,b,c,hab,hac,hbc,rfl⟩ := card_eq_three.mp hT
  have hleft (x y : Fin (3*q)) (hxy : x≠y) : A x y≠x := by
    intro h; have := hinj x (h.trans (hid x).symm); exact hxy this.symm
  have hright (x y : Fin (3*q)) (hxy : x≠y) : A x y≠y := by
    rw [hsym]; exact hleft y x hxy.symm
  have hsupport (x y z : Fin (3*q)) (hxy : x≠y) (hxz : x≠z) (hyz : y≠z) :
      ({x,y,A x y} : Finset (Fin (3*q)))={x,y,z} ↔ A x y=z :=
    wild_array_support_eq_three_iff x y z _ hxy hxz hyz (hleft x y hxy) (hright x y hxy)
  have hfilter : (univ.filter fun p : Fin (3*q) × Fin (3*q) =>
      p.1≠p.2 ∧ ({p.1,p.2,A p.1 p.2} : Finset (Fin (3*q)))={a,b,c}) =
      ({(a,b),(b,a),(a,c),(c,a),(b,c),(c,b)} : Finset (Fin (3*q) × Fin (3*q))).filter
        (fun p => p.1≠p.2 ∧ ({p.1,p.2,A p.1 p.2} : Finset (Fin (3*q)))={a,b,c}) := by
    ext p
    simp only [mem_filter,mem_univ,true_and]
    constructor
    · intro hp
      have hx : p.1∈({a,b,c} : Finset (Fin (3*q))) := by rw [← hp.2]; simp
      have hy : p.2∈({a,b,c} : Finset (Fin (3*q))) := by rw [← hp.2]; simp
      rcases p with ⟨x,y⟩
      simp only [mem_insert,mem_singleton] at hx hy
      rcases hx with rfl|rfl|rfl <;> rcases hy with rfl|rfl|rfl
      all_goals simp_all
    · exact fun h => h.2
  have hsba : ({b,a,A b a} : Finset (Fin (3*q)))={a,b,c} ↔ A a b=c := by
    rw [hsym b a,insert_comm]; exact hsupport a b c hab hac hbc
  have hsac : ({a,c,A a c} : Finset (Fin (3*q)))={a,b,c} ↔ A a c=b := by
    rw [show ({a,b,c} : Finset (Fin (3*q)))={a,c,b} by ext; simp [or_left_comm,or_comm]]
    exact hsupport a c b hac hab hbc.symm
  have hsca : ({c,a,A c a} : Finset (Fin (3*q)))={a,b,c} ↔ A a c=b := by
    rw [hsym c a,insert_comm]; exact hsac
  have hsbc : ({b,c,A b c} : Finset (Fin (3*q)))={a,b,c} ↔ A b c=a := by
    rw [show ({a,b,c} : Finset (Fin (3*q)))={b,c,a} by ext; simp [or_left_comm,or_comm,or_assoc]]
    exact hsupport b c a hbc hab.symm hac.symm
  have hscb : ({c,b,A c b} : Finset (Fin (3*q)))={a,b,c} ↔ A b c=a := by
    rw [hsym c b,insert_comm]; exact hsbc
  unfold wild_joint_multiplicity
  rw [hfilter]
  have ha : A a b≠a := hleft a b hab
  have hb : A a b≠b := hright a b hab
  have haca : A a c≠a := hleft a c hac
  have hacc : A a c≠c := hright a c hac
  have hbcb : A b c≠b := hleft b c hbc
  have hbcc : A b c≠c := hright b c hbc
  simp only [filter_insert,filter_singleton,Prod.fst,Prod.snd,hsupport a b c hab hac hbc,
    hsba,hsac,hsca,hsbc,hscb,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc,true_and]
  by_cases h1 : A a b=c <;> by_cases h2 : A a c=b <;> by_cases h3 : A b c=a
  all_goals simp [h1,h2,h3,hab,hac,hbc,Ne.symm hab,Ne.symm hac,Ne.symm hbc,
    Prod.mk.injEq,hsym b a,hsym c a,hsym c b,hid,ha,hb,haca,hacc,hbcb,hbcc]

lemma wild_joint_block_set_card (q : ℕ) (σ : Equiv.Perm (Fin (3*q))) (b : Fin q) :
    (wild_joint_block_set q σ b).card=3 := by
  classical
  let f : Fin 3 → Fin (3*q) := fun j => σ ⟨j.val+3*b.val,by have := j.isLt; have := b.isLt; omega⟩
  have hf : Function.Injective f := by
    intro x y h
    have hh := congrArg Fin.val (σ.injective h)
    apply Fin.ext; dsimp at hh; omega
  have heq : wild_joint_block_set q σ b=univ.image f := by
    ext v
    simp only [wild_joint_block_set,mem_filter,mem_univ,true_and,mem_image]
    constructor
    · intro h
      refine ⟨⟨(σ.symm v).val%3,Nat.mod_lt _ (by omega)⟩,?_⟩
      dsimp [f]
      apply σ.symm.injective
      simp only [Equiv.symm_apply_apply]
      apply Fin.ext
      have := Nat.mod_add_div (σ.symm v).val 3
      simp only [Fin.val_mk]; omega
    · rintro ⟨j,rfl⟩
      dsimp [f]; simp only [Equiv.symm_apply_apply,Fin.val_mk]
      have := j.isLt
      omega
  rw [heq,card_image_of_injective _ hf]
  simp

lemma wild_joint_block_set_mem (q : ℕ) (σ : Equiv.Perm (Fin (3*q))) (b : Fin q)
    (v : Fin (3*q)) : v∈wild_joint_block_set q σ b ↔ wild_joint_block q σ v=b := by
  simp [wild_joint_block_set,wild_joint_block,Fin.ext_iff]

/-- I(σ) = sum over blocks b of mu(block_b). -/
theorem wild_joint_invalid_count_eq_sum_multiplicity (q : ℕ) (A : Fin (3*q) → Fin (3*q) → Fin (3*q)) (hid : ∀ a, A a a = a) (hsym : ∀ a b, A a b = A b a) (hinj : ∀ a, Function.Injective (A a)) (σ : Equiv.Perm (Fin (3*q))) : wild_joint_invalid_count q A σ = ∑ b : Fin q, wild_joint_multiplicity q A (wild_joint_block_set q σ b) := by
  classical
  let C := fun b : Fin q => (wild_joint_block_set q σ b).filter
    (fun i => ∃ x∈wild_joint_block_set q σ b,∃ y∈wild_joint_block_set q σ b,x≠y ∧ A x y=i)
  have hd : (↑(univ : Finset (Fin q)) : Set (Fin q)).PairwiseDisjoint C := by
    intro b _ d _ hbd
    apply disjoint_left.mpr
    intro i hi hj
    have hb := (wild_joint_block_set_mem q σ b i).mp (mem_filter.mp hi).1
    have hd := (wild_joint_block_set_mem q σ d i).mp (mem_filter.mp hj).1
    exact hbd (hb.symm.trans hd)
  have heq : wild_joint_invalid_count q A σ=(univ.biUnion C).card := by
    unfold wild_joint_invalid_count
    congr 1
    ext i
    simp [C]
  rw [heq,card_biUnion hd]
  apply sum_congr rfl
  intro b _
  exact (wild_joint_multiplicity_eq_invalid_colors q A hid hsym hinj _
    (wild_joint_block_set_card q σ b)).symm
