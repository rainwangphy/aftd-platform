import AFTD.Prelude
import AFTD.Kb.Tcs.HalvingUpdate
import AFTD.Kb.Tcs.HalvingVoteFor
import AFTD.Kb.Tcs.V

/-!
# Halving.target_mem_update

Topic: learning   Node: 3b4ebd0fb7e0

Provenance: helper lemma. TCSlib, `Halving.target_mem_update`. Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/MistakeBounds/Halving.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Target survives its own update. Let $\mathtt{eval} : \mathit{Hyp} \to X \to \mathsf{Bool}$ be an evaluation map, let $V
\subseteq \mathit{Hyp}$ be a version space, fix an input $x \in X$, and let
$\mathtt{target} \in V$ be a hypothesis. Then $\mathtt{target}$ remains in the version
space obtained by updating $V$ on $x$ with the label that $\mathtt{target}$ itself
assigns, that is, $\mathtt{target} \in \mathtt{update}(\mathtt{eval}, V, x,
\mathtt{eval}\,\mathtt{target}\,x)$.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {Hyp X : Type*} in
/-- In the realizable setting the target hypothesis survives every update: if `target` lies in `V`, then it lies in the version space obtained by updating `V` on `x` with the label that `target` itself assigns to `x`. -/
lemma Halving.target_mem_update
    (eval : Hyp → X → Bool) (target : Hyp) (V : Finset Hyp) (x : X)
    (htarget : target ∈ V) :
    target ∈ update eval V x (eval target x) := by
  simp [update, voteFor, htarget]
