import AFTD.Prelude
import AFTD.Kb.Tcs.V

/-!
# ThreeSATToClique.Assignment

Topic: np_completeness   Node: db3495603893

Provenance: formalization of a published result. Source: TCSlib, `ThreeSATToClique.Assignment`. Lean proof by Yangshuo Zou, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/Complexity/NPReductions/ThreeSATToClique.lean (Copyright (c) 2026 Yangshuo Zou. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A truth valuation maps each variable to a proposition.
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
/-- A truth valuation maps each variable to a proposition. -/
def ThreeSATToClique.Assignment (V : Type) := V → Prop
