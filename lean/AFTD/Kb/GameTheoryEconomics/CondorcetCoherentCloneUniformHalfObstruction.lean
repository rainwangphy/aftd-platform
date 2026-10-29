import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetProductCloneUniformHalfObstruction
import AFTD.Kb.GameTheoryEconomics.CondorcetProductUniformHalfScoreObstruction
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.G

/-!
# condorcet_coherent_clone_uniform_half_obstruction

Topic: social_choice   Node: f99566f2634e

Provenance: helper lemma. IN-348 method diagnostic for OP-19, extending condorcet_product_clone_uniform_half_obstruction to fully permutation- and duplicate-coherent selectors. The base witness is condorcet_product_uniform_half_score_obstruction. Related product fixed-point method: https://theorydish.blog/2026/09/11/condorcet-quintets-a-proof-from-the-book/ . The finite mean-of-distinct-samples construction was audited in experiment8690; only this exact Lean statement is asserted. No election counterexample, general dimension bound, or research advance is claimed.

Suppose a root selector on m candidates is invariant under input permutations and the two multiplicity patterns of a two-candidate sample, has uniform iid output, and has strictly more than half of its claims satisfied by the identity ranking. For every natural k it has a lift with five-to-the-k clones of each candidate that preserves the base root, permutation invariance, duplicate-pattern coherence, and uniform output, together with an injective block ranking still satisfying strictly more than half the claims. The lift is a selector depending only on the sampled underlying set. Together with the proved23-candidate base witness this gives such obstructions with arbitrarily small uniform candidate masses. It obstructs a pointwise inference from raw iid uniform weights and flat marginals; it is not a failed election or a limitation of all selector-adapted weights.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

abbrev condorcet_coherent_clone_group (k : ℕ) := Fin k → ZMod 5

def condorcet_coherent_clone_mean {A : Type*} [DecidableEq A] {k : ℕ}
    (x y z : A × condorcet_coherent_clone_group k) : condorcet_coherent_clone_group k :=
  if x=y then
    if y=z then x.2 else 3*(x.2+z.2)
  else if x=z then 3*(x.2+y.2)
  else if y=z then 3*(x.2+y.2)
  else 2*(x.2+y.2+z.2)

def condorcet_coherent_clone_shift {A : Type*} {k : ℕ}
    (t : condorcet_coherent_clone_group k) (x : A × condorcet_coherent_clone_group k) := (x.1,x.2+t)

theorem condorcet_coherent_clone_shift_eq {A : Type*} {k : ℕ}
    (t : condorcet_coherent_clone_group k) (x y : A × condorcet_coherent_clone_group k) :
    condorcet_coherent_clone_shift t x=condorcet_coherent_clone_shift t y ↔ x=y := by
  simp [condorcet_coherent_clone_shift,Prod.ext_iff]

theorem condorcet_coherent_clone_mean_sym {A : Type*} [DecidableEq A] {k : ℕ}
    (x y z : A × condorcet_coherent_clone_group k) :
    condorcet_coherent_clone_mean x y z=condorcet_coherent_clone_mean y x z ∧
    condorcet_coherent_clone_mean x y z=condorcet_coherent_clone_mean x z y := by
  by_cases hxy : x=y <;> by_cases hxz : x=z <;> by_cases hyz : y=z
  all_goals simp_all [condorcet_coherent_clone_mean,eq_comm] <;> ring <;> simp_all

theorem condorcet_coherent_clone_mean_duplicate {A : Type*} [DecidableEq A] {k : ℕ}
    (x y : A × condorcet_coherent_clone_group k) :
    condorcet_coherent_clone_mean x x y=condorcet_coherent_clone_mean x y y := by
  by_cases h : x=y <;> simp [condorcet_coherent_clone_mean,h]

theorem condorcet_coherent_clone_mean_shift {A : Type*} [DecidableEq A] {k : ℕ}
    (t : condorcet_coherent_clone_group k) (x y z : A × condorcet_coherent_clone_group k) :
    condorcet_coherent_clone_mean (condorcet_coherent_clone_shift t x)
      (condorcet_coherent_clone_shift t y) (condorcet_coherent_clone_shift t z)=
        condorcet_coherent_clone_mean x y z+t := by
  have heq (u v : A × condorcet_coherent_clone_group k) :
      ((u.1,u.2+t) : A × condorcet_coherent_clone_group k)=(v.1,v.2+t) ↔ u=v :=
    condorcet_coherent_clone_shift_eq t u v
  simp only [condorcet_coherent_clone_mean,condorcet_coherent_clone_shift]
  simp only [heq]
  split_ifs <;> ext i <;> simp_all <;> ring_nf
  all_goals simp only [show (6 : ZMod 5)=1 from by decide,mul_one]

def condorcet_coherent_clone_root {A : Type*} [DecidableEq A] {k : ℕ}
    (f : A → A → A → A) (x y z : A × condorcet_coherent_clone_group k) :=
  (f x.1 y.1 z.1,
    x.2+condorcet_coherent_clone_mean (x.1,0) (y.1,y.2-x.2) (z.1,z.2-x.2))

theorem condorcet_coherent_clone_root_eq {A : Type*} [DecidableEq A] {k : ℕ}
    (f : A → A → A → A) (x y z : A × condorcet_coherent_clone_group k) :
    condorcet_coherent_clone_root f x y z=(f x.1 y.1 z.1,condorcet_coherent_clone_mean x y z) := by
  apply Prod.ext
  · rfl
  · have h := condorcet_coherent_clone_mean_shift x.2 (x.1,0)
      (y.1,y.2-x.2) (z.1,z.2-x.2)
    simpa [condorcet_coherent_clone_root,condorcet_coherent_clone_shift,add_comm] using h.symm

def condorcet_coherent_clone_fiber_equiv {A : Type*} [DecidableEq A] {k : ℕ}
    (f : A → A → A → A) (r : A × condorcet_coherent_clone_group k) :
    condorcet_product_clone_root_fiber (condorcet_coherent_clone_root f) r ≃
      condorcet_product_clone_root_fiber f r.1 ×
        (condorcet_coherent_clone_group k × condorcet_coherent_clone_group k) where
  toFun t := (⟨(t.val.1.1,t.val.2.1.1,t.val.2.2.1),
    congrArg Prod.fst t.property⟩,t.val.2.1.2-t.val.1.2,t.val.2.2.2-t.val.1.2)
  invFun t :=
    let g := condorcet_coherent_clone_mean (t.1.val.1,0) (t.1.val.2.1,t.2.1) (t.1.val.2.2,t.2.2)
    let a := r.2-g
    ⟨((t.1.val.1,a),(t.1.val.2.1,a+t.2.1),(t.1.val.2.2,a+t.2.2)),by
      apply Prod.ext t.1.property
      simp [condorcet_coherent_clone_root,a,g]⟩
  left_inv t := by
    apply Subtype.ext
    have h := congrArg Prod.snd t.property
    dsimp [condorcet_coherent_clone_root] at h
    have hg : r.2-condorcet_coherent_clone_mean (t.val.1.1,0)
        (t.val.2.1.1,t.val.2.1.2-t.val.1.2)
        (t.val.2.2.1,t.val.2.2.2-t.val.1.2)=t.val.1.2 := by
      rw [← h]
      abel
    dsimp
    rw [hg]
    simp
  right_inv t := by
    apply Prod.ext
    · apply Subtype.ext
      rfl
    · dsimp
      simp

theorem condorcet_coherent_clone_fiber_card {A : Type*} [Fintype A] [DecidableEq A] {k : ℕ}
    (f : A → A → A → A) (r : A × condorcet_coherent_clone_group k) :
    Fintype.card (condorcet_product_clone_root_fiber (condorcet_coherent_clone_root f) r)=
      Fintype.card (condorcet_product_clone_root_fiber f r.1)*(5^k)^2 := by
  rw [Fintype.card_congr (condorcet_coherent_clone_fiber_equiv f r)]
  simp [Fintype.card_fun,ZMod.card,pow_two]

def condorcet_coherent_clone_good_embedding {A B : Type*} [Fintype A] [Fintype B]
    (f : A → A → A → A) (F : (A × B) → (A × B) → (A × B) → (A × B))
    (hF : ∀ x y z,(F x y z).1=f x.1 y.1 z.1)
    (rank : A → ℕ) (ρ : B ≃ Fin (Fintype.card B)) :
    condorcet_product_clone_root_good f rank × (B × B × B) ↪
      condorcet_product_clone_root_good F
        (fun x => Fintype.card B*rank x.1+(ρ x.2).val) where
  toFun t :=
    ⟨((t.1.val.1,t.2.1),(t.1.val.2.1,t.2.2.1),(t.1.val.2.2,t.2.2.2)),by
      obtain ⟨h₁,h₂,h₃⟩ := t.1.property
      have hr := (ρ (F (t.1.val.1,t.2.1) (t.1.val.2.1,t.2.2.1)
        (t.1.val.2.2,t.2.2.2)).2).isLt
      change
        Fintype.card B*rank (F _ _ _).1+_ < Fintype.card B*rank t.1.val.1+_ ∧
        Fintype.card B*rank (F _ _ _).1+_ < Fintype.card B*rank t.1.val.2.1+_ ∧
        Fintype.card B*rank (F _ _ _).1+_ < Fintype.card B*rank t.1.val.2.2+_
      rw [hF]
      constructor
      · nlinarith
      constructor <;> nlinarith⟩
  inj' := by
    intro x y h
    have hval := congrArg Subtype.val h
    apply Prod.ext
    · apply Subtype.ext
      exact Prod.ext (congrArg (fun t => t.1.1) hval)
        (Prod.ext (congrArg (fun t => t.2.1.1) hval)
          (congrArg (fun t => t.2.2.1) hval))
    · exact Prod.ext (congrArg (fun t => t.1.2) hval)
        (Prod.ext (congrArg (fun t => t.2.1.2) hval)
          (congrArg (fun t => t.2.2.2) hval))

theorem condorcet_coherent_clone_uniform_half_obstruction
    (m k : ℕ) (f : Fin m → Fin m → Fin m → Fin m)
    (hsym : ∀ a b c,f a b c=f b a c ∧ f a b c=f a c b)
    (hdup : ∀ a b,f a a b=f a b b)
    (huniform : ∀ r : Fin m,Fintype.card (condorcet_product_clone_root_fiber f r)=m^2)
    (hscore : m^3 < 2*Fintype.card (condorcet_product_clone_root_good f Fin.val)) :
    let G := condorcet_coherent_clone_group k
    let ρ := Fintype.equivFin G
    ∃ F : (Fin m × G) → (Fin m × G) → (Fin m × G) → (Fin m × G),
      (∀ x y z,(F x y z).1=f x.1 y.1 z.1) ∧
      (∀ x y z,F x y z=F y x z ∧ F x y z=F x z y) ∧
      (∀ x y,F x x y=F x y y) ∧
      (∀ r,Fintype.card (condorcet_product_clone_root_fiber F r)=(m*5^k)^2) ∧
      Function.Injective (fun x : Fin m × G => 5^k*x.1.val+(ρ x.2).val) ∧
      (m*5^k)^3 < 2*Fintype.card
        (condorcet_product_clone_root_good F (fun x => 5^k*x.1.val+(ρ x.2).val)) := by
  classical
  dsimp only
  let F := @condorcet_coherent_clone_root (Fin m) _ k f
  have hF : ∀ x y z,(F x y z).1=f x.1 y.1 z.1 := fun _ _ _ => rfl
  have hcard : Fintype.card (condorcet_coherent_clone_group k)=5^k := by
    simp [condorcet_coherent_clone_group,Fintype.card_fun,ZMod.card]
  refine ⟨F,hF,?_,?_,?_,?_,?_⟩
  · intro x y z
    dsimp [F]
    simp only [condorcet_coherent_clone_root_eq]
    exact ⟨Prod.ext (hsym _ _ _).1 (condorcet_coherent_clone_mean_sym x y z).1,
      Prod.ext (hsym _ _ _).2 (condorcet_coherent_clone_mean_sym x y z).2⟩
  · intro x y
    dsimp [F]
    simp only [condorcet_coherent_clone_root_eq]
    exact Prod.ext (hdup _ _) (condorcet_coherent_clone_mean_duplicate x y)
  · intro r
    rw [condorcet_coherent_clone_fiber_card,huniform]
    ring
  · intro x y h
    have he : finProdFinEquiv (x.1,Fintype.equivFin _ x.2)=
        finProdFinEquiv (y.1,Fintype.equivFin _ y.2) := by
      apply Fin.ext
      simpa only [finProdFinEquiv,Equiv.coe_fn_mk,hcard,add_comm] using h
    have he' := finProdFinEquiv.injective he
    apply Prod.ext
    · exact congrArg (fun p : Fin m × Fin (Fintype.card (condorcet_coherent_clone_group k)) => p.1) he'
    · apply (Fintype.equivFin (condorcet_coherent_clone_group k)).injective
      exact congrArg (fun p : Fin m × Fin (Fintype.card (condorcet_coherent_clone_group k)) => p.2) he'
  · have hc := Fintype.card_le_of_injective
      (condorcet_coherent_clone_good_embedding f F hF Fin.val (Fintype.equivFin _)).toFun
      (condorcet_coherent_clone_good_embedding f F hF Fin.val (Fintype.equivFin _)).injective
    have hc' : Fintype.card (condorcet_product_clone_root_good f Fin.val)*(5^k)^3 ≤
        Fintype.card (condorcet_product_clone_root_good F
          (fun x => 5^k*x.1.val+(Fintype.equivFin _ x.2).val)) := by
      simpa only [Fintype.card_prod,hcard,pow_succ,pow_zero,mul_one,one_mul,mul_assoc] using hc
    calc
      (m*5^k)^3 = m^3*(5^k)^3 := mul_pow _ _ _
      _ < (2*Fintype.card (condorcet_product_clone_root_good f Fin.val))*(5^k)^3 :=
        Nat.mul_lt_mul_of_pos_right hscore (by positivity)
      _ = 2*(Fintype.card (condorcet_product_clone_root_good f Fin.val)*(5^k)^3) := by ring
      _ ≤ _ := Nat.mul_le_mul_left 2 hc'
