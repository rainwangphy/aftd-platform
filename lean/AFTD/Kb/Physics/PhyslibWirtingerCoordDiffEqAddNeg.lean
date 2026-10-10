import AFTD.Prelude

/-!
# Physlib.Wirtinger.coordDiff_eq_add_neg

Topic: classical_mechanics   Node: 9755ed03c107

Provenance: formalization of a published result. Source: Physlib, `Physlib.Wirtinger.coordDiff_eq_add_neg`. Lean proof by Andrea Pari, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/Physlib/Mathematics/Calculus/Wirtinger/Coordinate.lean (Copyright (c) 2026 Andrea Pari. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The coordinate difference `z^J − z̄^J` as a sum of the holomorphic coordinate and the negated conjugate coordinate — the form on which the `dWirtingerCoord` / `dWirtingerAntiCoord` additivity rules apply.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
variable {ι : Type*} in
variable [Fintype ι] [DecidableEq ι] in
variable {f g : (ι → ℂ) → ℂ} in
omit [Fintype ι] [DecidableEq ι] in
/-- The coordinate difference `z^J − z̄^J` as a sum of the holomorphic coordinate and the negated conjugate coordinate — the form on which the `dWirtingerCoord` / `dWirtingerAntiCoord` additivity rules apply. -/
lemma Physlib.Wirtinger.coordDiff_eq_add_neg (J : ι) :
    (fun v : (ι → ℂ) => v J - star (v J))
      = (fun v => v J) + (fun v => -(star (v J))) :=
  funext fun v => sub_eq_add_neg (v J) (star (v J))
