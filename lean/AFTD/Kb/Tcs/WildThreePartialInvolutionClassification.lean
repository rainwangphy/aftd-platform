import AFTD.Prelude

/-!
# wild_three_partial_involution_classification

Topic: graphs   Node: f0fd00d43144

Provenance: helper lemma. IN-382 / OP-306 campaign9, 2026-10-30. Standard finite matching symmetry supporting the mixed-moment route for https://arxiv.org/html/2610.22142v1. Exact experiment9566 exposed the missing parity assumption. The original false helper remains retired and its proof record is preserved. No wild-number bound or research advance is claimed.

On three vertices, two symmetric partial partner maps, each with at most one fixed point, are isomorphic whenever the existence of a fixed point and of a non-loop internal edge agree. This is a finite classification checked by Lean kernel reduction.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 6000000
set_option maxRecDepth 100000
set_option synthInstance.maxSize 10000
attribute [local instance] Fintype.decidableForallFintype Fintype.decidableExistsFintype

theorem wild_three_partial_involution_classification :
    ∀ f g : Fin 3 → Option (Fin 3),
      (∀ j k, f j = some k ↔ f k = some j) →
      (∀ j k, g j = some k ↔ g k = some j) →
      (∀ j k, f j = some j → f k = some k → j = k) →
      (∀ j k, g j = some j → g k = some k → j = k) →
      ((∃ j, f j = some j) ↔ ∃ j, g j = some j) →
      ((∃ j k, j ≠ k ∧ f j = some k) ↔ ∃ j k, j ≠ k ∧ g j = some k) →
      ∃ r : Fin 3 → Fin 3, Function.Bijective r ∧
        ∀ j k, f j = some k ↔ g (r j) = some (r k) := by
  unfold Function.Bijective Function.Injective Function.Surjective
  decide +kernel
