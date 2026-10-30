import AFTD.Prelude
import AFTD.Kb.Tcs.WildJointCanonicalMatchingIsInvolution
import AFTD.Kb.Tcs.WildInvolutionsConjugateOfFixedCount
import AFTD.Kb.Tcs.WildJointCanonicalMatching

/-!
# wild_normalized_color_canonical_isomorphism

Topic: graphs   Node: 13b9d4d7d115

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite matching symmetry and exact permutation conditioning supporting wild_joint_expected_ID_eq_alpha_sum. This uses the corrected odd-q orbit theorem; it does not establish the main weighted sign or a new wild-number bound.

For odd q>=3, every chosen color of a symmetric idempotent row-injective array on Fin(3q) is carried to the canonical matching by a vertex permutation sending its unique missing vertex to0.
-/

open Finset
open scoped BigOperators Classical
set_option maxHeartbeats 6000000
set_option maxRecDepth 20000
set_option synthInstance.maxSize 10000

theorem wild_normalized_color_canonical_isomorphism
    (q : ℕ) (hq : 3 ≤ q) (hodd : q % 2 = 1)
    (A : Fin (3*q) → Fin (3*q) → Fin (3*q))
    (hid : ∀ x, A x x = x) (hsym : ∀ x y, A x y = A y x)
    (hinj : ∀ x, Function.Injective (A x)) (i : Fin (3*q)) :
    ∃ e : Equiv.Perm (Fin (3*q)), e i = (⟨0,by omega⟩ : Fin (3*q)) ∧
      ∀ x y, wild_joint_canonical_matching q (e x) (e y) ↔ x ≠ y ∧ A x y = i := by
  classical
  let row : Fin (3*q) → Equiv.Perm (Fin (3*q)) := fun x =>
    Equiv.ofBijective (A x) ⟨hinj x,Finite.surjective_of_injective (hinj x)⟩
  let p : Fin (3*q) → Fin (3*q) := fun x => (row x).symm i
  have hpA : ∀ x, A x (p x) = i := fun x => (row x).apply_symm_apply i
  have hp : Function.Involutive p := by
    intro x; apply hinj (p x); rw [hpA,hsym,hpA]
  have hpfix : ∀ x, p x = x ↔ x = i := by
    intro x
    constructor
    · intro h; have hh := hpA x; rwa [h,hid] at hh
    · intro h; rw [h]; apply hinj i; rw [hpA,hid]
  let f : Equiv.Perm (Fin (3*q)) := ⟨p,p,hp,hp⟩
  obtain ⟨g,hg,hgfix,hgR⟩ := wild_joint_canonical_matching_is_involution q hq hodd
  have hcard : (univ.filter fun x => f x = x).card =
      (univ.filter fun x => g x = x).card := by
    change (univ.filter fun x => p x = x).card = _
    simp only [hpfix,hgfix,filter_eq',mem_univ,if_true,card_singleton]
  obtain ⟨e,he⟩ := wild_involutions_conjugate_of_fixed_count f g hp hg hcard
  have hei : e i = (⟨0,by omega⟩ : Fin (3*q)) := by
    apply (hgfix _).mp
    rw [← he]
    exact congrArg e ((hpfix i).mpr rfl)
  refine ⟨e,hei,?_⟩
  intro x y
  rw [hgR,← he]
  simp only [e.injective.eq_iff,ne_eq]
  change (¬x = y ∧ p x = y) ↔ ¬x = y ∧ A x y = i
  constructor
  · rintro ⟨hxy,hp⟩; exact ⟨hxy,hp ▸ hpA x⟩
  · rintro ⟨hxy,ha⟩
    exact ⟨hxy,hinj x ((hpA x).trans ha.symm)⟩
