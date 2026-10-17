import AFTD.Prelude

/-!
# ENNReal.tendsto_toReal_iff_of_eventually_ne_top

Topic: quantum   Node: 502fc0a8ee16

Provenance: formalization of a published result. Source: QuantumInfo, `ENNReal.tendsto_toReal_iff_of_eventually_ne_top`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ForMathlib/Filter.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

ENNReal.tendsto_toReal_iff_of_eventually_ne_top
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Topology in
open Filter Topology ENNReal in
theorem ENNReal.tendsto_toReal_iff_of_eventually_ne_top
  {ι} {fi : Filter ι} {f : ι → ℝ≥0∞} (hf : ∀ᶠ i in fi, f i ≠ ∞) {x : ℝ≥0∞}
    (hx : x ≠ ∞) : Tendsto (fun n => (f n).toReal) fi (𝓝 x.toReal) ↔ Tendsto f fi (𝓝 x) := by
  have he₁ : f =ᶠ[fi] (fun n ↦ (f n).toNNReal) := by
    rw [EventuallyEq]
    filter_upwards [hf] with i h
    simp [h]
  have he₂ : (fun n ↦ (f n).toReal) = (fun n ↦ ((f n).toNNReal : ℝ≥0∞).toReal) :=
    rfl
  rw [Filter.tendsto_congr' he₁, he₂]
  exact tendsto_toReal_iff (by finiteness) hx
