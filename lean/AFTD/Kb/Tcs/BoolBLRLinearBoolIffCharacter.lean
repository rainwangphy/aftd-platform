import AFTD.Prelude
import AFTD.Kb.Tcs.BoolBLRIsLinearBool
import AFTD.Kb.Tcs.BoolBLRLiftPm1
import AFTD.Kb.Tcs.BoolBLRLinearBoolIffCharacterAuxHEqH
import AFTD.Kb.Tcs.BoolBLRLinearBoolIffCharacterAuxHFx
import AFTD.Kb.Tcs.BoolFourierBoolToPM1
import AFTD.Kb.Tcs.BoolFourierCharS
import AFTD.Kb.Tcs.BoolFourierHypercube
import AFTD.Kb.Tcs.BoolFourierXorVec
import AFTD.Kb.Tcs.BooleanAnalysisChiS
import AFTD.Kb.Tcs.BooleanAnalysisInnerProductChiSelf

/-!
# BoolBLR.linear_bool_iff_character

Topic: interactive   Node: c3e96904d200

Provenance: helper lemma. TCSlib, `BoolBLR.linear_bool_iff_character`. Lean proof by Prastik Mohanraj, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/BooleanAnalysis/BLR/BoolBLR.lean (Copyright (c) 2026 Prastik Mohanraj. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Linear Boolean functions are exactly the Walsh characters. Let $f : \{0,1\}^n \to \{0,1\}$ be a Boolean function. Then $f$ is linear — that is,
$f(x \oplus y) = f(x) \oplus f(y)$ for all $x, y \in \{0,1\}^n$, where $\oplus$ denotes
bitwise XOR — if and only if there exists a set $S \subseteq [n]$ for which the $\pm 1$
lift $x \mapsto (-1)^{f(x)}$ coincides with the Walsh character $\chi_S(x) = \prod_{i
\in S}(-1)^{x_i}$.
-/

set_option autoImplicit true in
set_option relaxedAutoImplicit true in
open Finset BoolFourier in
/-- Characterizes Boolean linear functions as functions whose `{±1}` lift is a Fourier character. **Source:** [OD14, §1.6]. -/
lemma BoolBLR.linear_bool_iff_character {n : ℕ} (f : hypercube n → Bool) :
  is_linear_bool f ↔ ∃ S, lift_pm1 f = char_S S := by
  classical
  refine' ⟨ fun hf => _, _ ⟩;
  -- (=>) Given linearity, construct S explicitly as the support of f on basis vectors.
  · use Finset.univ.filter fun i => f ( fun j => if j = i then true else false ) = true;
    funext x;
    -- Express f(x) in terms of f on basis vectors using linearity:
    -- f(x) = ⨁_{i : x_i = true} f(e_i).
    let h_fx : f x = if (∑ i ∈ Finset.univ.filter (fun i => x i), if f (fun j => if j = i then true else false) then 1 else 0) % 2 = 0 then false else true := (linear_bool_iff_character_aux_h_fx f hf x)

    -- Now compare lift_pm1 f x with the character: both equal (-1)^{(parity)}.
    unfold lift_pm1 char_S; simp +decide [ h_fx ] ; simp only [BooleanAnalysis.chiS] ;
    rw [ Finset.prod_congr rfl fun i hi => show BoolToPM1 ( x i ) = if x i = true then -1 else 1 from by cases x i <;> rfl ] ; simp +decide [ Finset.prod_ite ] ; ring_nf;
    -- Two cases on parity, both check by hand.
    cases Nat.mod_two_eq_zero_or_one ( Finset.card ( Finset.filter ( fun i => ( f fun j => decide ( j = i ) ) = true ) ( Finset.filter ( fun i => x i = true ) Finset.univ ) ) ) <;> simp +decide [*];
    · simp_all +decide [Finset.filter_filter];
      simp_all +decide [and_comm];
      rw [ ← Nat.mod_add_div ( Finset.card _ ) 2, ‹Finset.card _ % 2 = 0› ] ; norm_num [ pow_add, pow_mul ];
    · simp_all +decide [Finset.filter_filter];
      simp_all +decide [and_comm];
      rw [ ← Nat.mod_add_div ( Finset.card _ ) 2, ‹Finset.card _ % 2 = 1› ] ; norm_num [ pow_add, pow_mul, BoolToPM1 ];
  -- (<=) If lift_pm1 f = χ_S, then f is linear via the multiplicativity of χ_S.
  · rintro ⟨ S, hS ⟩ x y;
    -- The key fact: χ_S(x ⊕ y) = χ_S(x) χ_S(y), since BoolToPM1 turns XOR into multiplication.
    unfold lift_pm1 at hS;
    -- Since (-1) is injective on Bool, equality of ±1 lifts gives equality of bits.
    let h_eq : BoolToPM1 (f (xor_vec x y)) = BoolToPM1 (Bool.xor (f x) (f y)) := (linear_bool_iff_character_aux_h_eq_h f S hS x y)

    cases h1 : f (xor_vec x y) <;> cases h2 : f x <;> cases h3 : f y <;>
      simp_all [Bool.xor] <;> (simp only [*] at h_eq; norm_num at h_eq)
