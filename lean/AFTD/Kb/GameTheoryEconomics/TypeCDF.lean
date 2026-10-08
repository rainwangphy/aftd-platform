import AFTD.Prelude

/-!
# TypeCDF

Topic: mechanism_design   Node: 8757a6f4e5b3

Provenance: formalization of a published result. Source: EconCSLib, `TypeCDF`. Lean proof by xbei (from the file's git history), from https://github.com/gametheoryinlean/EconCSLib/blob/1a88f809b538365c89ae7b3d3fb53a20f63f3951/EconCSLib/MechanismDesign/Auction/BayesianSingleItem.lean (Copyright (c) 2026 EconCSLib contributors. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

A scalar type distribution on the interval `[0, ω]`, recorded by its CDF.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open MeasureTheory in
/-- A scalar type distribution on the interval `[0, ω]`, recorded by its CDF. -/
structure TypeCDF (ω : ℝ) where
  /-- Upper bound of the support interval is nonnegative. -/
  omega_nonneg : 0 ≤ ω
  /-- Cumulative distribution function. -/
  cdf : ℝ → ℝ
  /-- Monotonicity of the CDF on the support interval. -/
  monotoneOn_cdf : MonotoneOn cdf (Set.Icc 0 ω)
  /-- Normalization at the lower endpoint. -/
  cdf_zero : cdf 0 = 0
  /-- Normalization at the upper endpoint. -/
  cdf_upper : cdf ω = 1
  /-- Smoothness assumption used in continuous-type auction theory. -/
  differentiableOn_cdf : DifferentiableOn ℝ cdf (Set.Ioo 0 ω)
