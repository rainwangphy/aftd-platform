import AFTD.Prelude

/-!
# Mixable

Topic: information   Node: c95967524632

Provenance: formalization of a published result. Source: QuantumInfo, `Mixable`. Lean proof by Alex Meiburg, from https://github.com/leanprover-community/physlib/blob/e411c6e89692e83bc67fe451302ae7f82cf39b10/QuantumInfo/ClassicalInfo/Prob.lean (Copyright (c) 2025 Alex Meiburg. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A `Mixable T` typeclass instance gives a compact way of talking about the action of probabilities for forming linear combinations in convex spaces. The notation `p [ x₁ ↔ x₂ ]` means to take a convex combination, equal to `x₁` if `p=1` and to `x₂` if `p=0`. Mixable is defined by an "underlying" data type `U` with addition and scalar multiplication, and a bijection between the `T` and a convex set of `U`. For instance, in `Mixable (Distribution (Fin n))`, `U` is `n`-element vectors (which form the probability simplex, degenerate in one dimension). For `QuantumInfo.States.Mixed.MState` density matrices in quantum mechanics, which are PSD matrices of trace 1, `U` is the underlying matrix. Why not just stick with existing notions of `Convex`? `Convex` requires that the type already forms an `AddCommMonoid` and `Module ℝ`. But many types, such as `Distribution`, are not: there is no good notion of "multiplying a probability distribution by 0.3" to get another distribution. We can coerce the distribution nto, say, a vector or a function, but then we are not doing arithmetic with distributions. Accordingly, the expression `0.3 * distA + 0.7 * distB` cannot represent a distribution on its own.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open NNReal in
open Classical in
/-- A `Mixable T` typeclass instance gives a compact way of talking about the action of probabilities for forming linear combinations in convex spaces. The notation `p [ x₁ ↔ x₂ ]` means to take a convex combination, equal to `x₁` if `p=1` and to `x₂` if `p=0`. Mixable is defined by an "underlying" data type `U` with addition and scalar multiplication, and a bijection between the `T` and a convex set of `U`. For instance, in `Mixable (Distribution (Fin n))`, `U` is `n`-element vectors (which form the probability simplex, degenerate in one dimension). For `QuantumInfo.States.Mixed.MState` density matrices in quantum mechanics, which are PSD matrices of trace 1, `U` is the underlying matrix. Why not just stick with existing notions of `Convex`? `Convex` requires that the type already forms an `AddCommMonoid` and `Module ℝ`. But many types, such as `Distribution`, are not: there is no good notion of "multiplying a probability distribution by 0.3" to get another distribution. We can coerce the distribution nto, say, a vector or a function, but then we are not doing arithmetic with distributions. Accordingly, the expression `0.3 * distA + 0.7 * distB` cannot represent a distribution on its own. -/
class Mixable (U : outParam (Type u)) (T : Type v) [AddCommMonoid U] [Module ℝ U] where
  /-- Getter for the underlying data -/
  to_U : T → U
  /-- Proof that this getter is injective -/
  to_U_inj : ∀ {T₁ T₂}, to_U T₁ = to_U T₂ → T₁ = T₂
  /-- Proof that this image is convex -/
  convex : Convex ℝ (Set.range to_U)
  /-- Function to get a T from a proof that U is in the set. -/
  mkT : {u : U} → (∃ t, to_U t = u) → { t : T // to_U t = u }
