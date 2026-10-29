import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.TotalPreorder
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder

/-!
# condorcet_product_clone_uniform_half_obstruction

Topic: social_choice   Node: 54cac5c11060

Provenance: helper lemma. IN-348 supporting lemma for the limitation of raw product-invariance certificates in OP-19. The base finite diagnostic is condorcet_product_uniform_half_score_obstruction. This general lift shows that arbitrarily small individual candidate masses alone do not repair the pointwise inference for ordered-tuple root maps. It supplies no election counterexample and does not obstruct selector-adapted weights or another fixed point. No research advance is claimed.

For a root map on ordered triples of m candidates, suppose each root has exactly m squared preimages under uniform iid sampling and the identity ranking satisfies strictly more than half the claims. For every positive k, there is a lifted root map on m times k candidates, represented as base-candidate and clone pairs, with exactly (m times k) squared preimages per root and strictly more than half the claims satisfied by the injective block rank k times base position plus clone position. The lifted root has the original root as its base coordinate. This lift carries the first sampled clone coordinate to the root and can depend on the ordered tuple; permutation or underlying-set invariance is not asserted.
-/

open Finset
open scoped BigOperators

set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

-- This lift permits the root to depend on the ordered tuple. The finite
-- 23-candidate witness is stronger: there the root depends only on its set.
def condorcet_product_clone_clone_root {A B : Type*} (f : A → A → A → A)
    (x y z : A × B) : A × B := (f x.1 y.1 z.1, x.2)

abbrev condorcet_product_clone_root_fiber {A : Type*} (f : A → A → A → A) (r : A) :=
  {t : A × A × A // f t.1 t.2.1 t.2.2 = r}

abbrev condorcet_product_clone_root_good {A : Type*} (f : A → A → A → A) (rank : A → ℕ) :=
  {t : A × A × A // rank (f t.1 t.2.1 t.2.2) < rank t.1 ∧
    rank (f t.1 t.2.1 t.2.2) < rank t.2.1 ∧
    rank (f t.1 t.2.1 t.2.2) < rank t.2.2}

def condorcet_product_clone_clone_fiber_equiv {A B : Type*} (f : A → A → A → A) (r : A × B) :
    condorcet_product_clone_root_fiber (condorcet_product_clone_clone_root f) r ≃
      condorcet_product_clone_root_fiber f r.1 × (B × B) where
  toFun t := (⟨(t.val.1.1,t.val.2.1.1,t.val.2.2.1),
    congrArg Prod.fst t.property⟩,t.val.2.1.2,t.val.2.2.2)
  invFun t := ⟨((t.1.val.1,r.2),(t.1.val.2.1,t.2.1),(t.1.val.2.2,t.2.2)),
    Prod.ext t.1.property rfl⟩
  left_inv t := by
    apply Subtype.ext
    have h := congrArg Prod.snd t.property
    exact Prod.ext (Prod.ext rfl h.symm) rfl
  right_inv t := by rfl

theorem condorcet_product_clone_clone_fiber_card {A B : Type*} [Fintype A] [Fintype B]
    [DecidableEq A] [DecidableEq B] (f : A → A → A → A) (r : A × B) :
    Fintype.card (condorcet_product_clone_root_fiber (condorcet_product_clone_clone_root f) r) =
      Fintype.card (condorcet_product_clone_root_fiber f r.1) * (Fintype.card B)^2 := by
  rw [Fintype.card_congr (condorcet_product_clone_clone_fiber_equiv f r)]
  simp [pow_two]

def condorcet_product_clone_clone_good_embedding {A : Type*} [Fintype A]
    (k : ℕ) (f : A → A → A → A) (rank : A → ℕ) :
    condorcet_product_clone_root_good f rank × (Fin k × Fin k × Fin k) ↪
      condorcet_product_clone_root_good (condorcet_product_clone_clone_root f)
        (fun x : A × Fin k => k * rank x.1 + x.2.val) where
  toFun t :=
    ⟨((t.1.val.1,t.2.1),(t.1.val.2.1,t.2.2.1),(t.1.val.2.2,t.2.2.2)),by
      obtain ⟨h₁,h₂,h₃⟩ := t.1.property
      have hb₁ := t.2.1.isLt
      have hb₂ := t.2.2.1.isLt
      have hb₃ := t.2.2.2.isLt
      change
        k * rank (f t.1.val.1 t.1.val.2.1 t.1.val.2.2) + t.2.1.val <
          k * rank t.1.val.1 + t.2.1.val ∧
        k * rank (f t.1.val.1 t.1.val.2.1 t.1.val.2.2) + t.2.1.val <
          k * rank t.1.val.2.1 + t.2.2.1.val ∧
        k * rank (f t.1.val.1 t.1.val.2.1 t.1.val.2.2) + t.2.1.val <
          k * rank t.1.val.2.2 + t.2.2.2.val
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

theorem condorcet_product_clone_clone_good_card {A : Type*} [Fintype A] [DecidableEq A]
    (k : ℕ) (f : A → A → A → A) (rank : A → ℕ) :
    Fintype.card (condorcet_product_clone_root_good f rank) * k^3 ≤
      Fintype.card (condorcet_product_clone_root_good (condorcet_product_clone_clone_root (B := Fin k) f)
        (fun x => k * rank x.1 + x.2.val)) := by
  have h := Fintype.card_le_of_injective
    (condorcet_product_clone_clone_good_embedding k f rank).toFun
    (condorcet_product_clone_clone_good_embedding k f rank).injective
  simpa [Fintype.card_prod, pow_succ, mul_assoc] using h

theorem condorcet_product_clone_uniform_half_obstruction
    (m k : ℕ) (hk : 0 < k) (f : Fin m → Fin m → Fin m → Fin m)
    (huniform : ∀ r : Fin m,Fintype.card (condorcet_product_clone_root_fiber f r)=m^2)
    (hscore : m^3 < 2*Fintype.card (condorcet_product_clone_root_good f Fin.val)) :
    ∃ F : (Fin m × Fin k) → (Fin m × Fin k) → (Fin m × Fin k) → (Fin m × Fin k),
      (∀ x y z,(F x y z).1=f x.1 y.1 z.1) ∧
      (∀ r,Fintype.card (condorcet_product_clone_root_fiber F r)=(m*k)^2) ∧
      Function.Injective (fun x : Fin m × Fin k => k*x.1.val+x.2.val) ∧
      (m*k)^3 < 2*Fintype.card (condorcet_product_clone_root_good F (fun x => k*x.1.val+x.2.val)) := by
  refine ⟨condorcet_product_clone_clone_root f,fun _ _ _ => rfl,?_,?_,?_⟩
  · intro r
    rw [condorcet_product_clone_clone_fiber_card,huniform,Fintype.card_fin]
    ring
  · intro x y h
    apply finProdFinEquiv.injective
    apply Fin.ext
    simpa only [finProdFinEquiv,Equiv.coe_fn_mk,add_comm] using h
  · have hc := condorcet_product_clone_clone_good_card k f Fin.val
    calc
      (m*k)^3 = m^3*k^3 := mul_pow m k 3
      _ < (2*Fintype.card (condorcet_product_clone_root_good f Fin.val))*k^3 :=
        Nat.mul_lt_mul_of_pos_right hscore (pow_pos hk 3)
      _ = 2*(Fintype.card (condorcet_product_clone_root_good f Fin.val)*k^3) := by ring
      _ ≤ 2*Fintype.card (condorcet_product_clone_root_good (condorcet_product_clone_clone_root (B := Fin k) f)
        (fun x : Fin m × Fin k => k*x.1.val+x.2.val)) := Nat.mul_le_mul_left 2 hc
