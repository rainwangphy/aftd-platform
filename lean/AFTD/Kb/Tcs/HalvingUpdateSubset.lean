import AFTD.Prelude
import AFTD.Kb.Tcs.HalvingUpdate

/-!
# Halving.update_subset

Topic: learning   Node: df2b8ffa4537

Provenance: helper lemma. TCSlib, `Halving.update_subset`. Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/MistakeBounds/Halving.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

The updated version space is a subset. Fix an evaluation map $\mathtt{eval} : \mathit{Hyp} \to X \to \mathsf{Bool}$, a finite
version space $V \subseteq \mathit{Hyp}$, an input $x \in X$, and a label $y \in
\mathsf{Bool}$. Then the updated version space is contained in the original one:
$\mathtt{update}(\mathtt{eval}, V, x, y) \subseteq V$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {Hyp X : Type*} in
/-- Updating the version space on a labelled example only removes hypotheses: the updated version space `update eval V x y` is a subset of the old version space `V`. -/
lemma Halving.update_subset
    (eval : Hyp → X → Bool) (V : Finset Hyp) (x : X) (y : Bool) :
    update eval V x y ⊆ V := by
  intro h hh
  have hh' : h ∈ V ∧ eval h x = y := by
    simpa [update, voteFor] using hh
  exact hh'.1
