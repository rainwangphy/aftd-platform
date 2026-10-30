import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointCanonicalMatching

/-!
# wild_joint_canonical_matching_is_involution

Topic: graphs   Node: 0335cce1d624

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite matching symmetry supporting the mixed-moment route for https://arxiv.org/html/2610.22142v1. Exact experiment9566 exposed the missing parity assumption. The original false helper remains retired and its proof record is preserved. No wild-number bound or research advance is claimed.

For odd q>=3, the canonical matching on Fin(3q) is precisely the off-diagonal part of an involution whose unique fixed point is0. The odd-q hypothesis prevents an extra isolated vertex.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 10000

theorem wild_joint_canonical_matching_is_involution
    (q : ℕ) (hq : 3 ≤ q) (hodd : q % 2 = 1) :
    ∃ f : Equiv.Perm (Fin (3*q)), Function.Involutive f ∧
      (∀ x, f x = x ↔ x = (⟨0,by omega⟩ : Fin (3*q))) ∧
      ∀ x y, wild_joint_canonical_matching q x y ↔ x ≠ y ∧ f x = y := by
  let p : Fin (3*q) → Fin (3*q) := fun x =>
    ⟨if x.val = 0 then 0 else if x.val % 2 = 1 then x.val+1 else x.val-1, by
      have hx := x.isLt
      split_ifs <;> omega⟩
  have hp : Function.Involutive p := by
    intro x
    apply Fin.ext
    by_cases hx0 : x.val = 0
    · simp [p,hx0]
    · by_cases hxodd : x.val % 2 = 1
      · have hn : x.val+1 ≠ 0 := by omega
        have heven : (x.val+1)%2 ≠ 1 := by omega
        simp [p,hx0,hxodd,hn,heven]
      · have hn : x.val-1 ≠ 0 := by omega
        have hprev : (x.val-1)%2 = 1 := by omega
        simp [p,hx0,hxodd,hn,hprev]
        omega
  refine ⟨⟨p,p,hp,hp⟩,hp,?_,?_⟩
  · intro x
    change p x = x ↔ x = (⟨0,by omega⟩ : Fin (3*q))
    simp only [Fin.ext_iff,p]
    split_ifs <;> omega
  · intro x y
    change wild_joint_canonical_matching q x y ↔ x ≠ y ∧ p x = y
    simp only [wild_joint_canonical_matching,Fin.ext_iff,p]
    have hx := x.isLt
    have hy := y.isLt
    rcases le_total x.val y.val with h|h
    · rw [min_eq_left h,max_eq_right h]
      split_ifs <;> omega
    · rw [min_eq_right h,max_eq_left h]
      split_ifs <;> omega
