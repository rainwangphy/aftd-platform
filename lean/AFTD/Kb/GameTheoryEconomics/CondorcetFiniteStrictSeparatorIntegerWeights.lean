import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.CondorcetDimensionLeThreeIffAcyclicWeightSeparation

/-!
# condorcet_finite_strict_separator_integer_weights

Topic: social_choice   Node: eabba68dbbbd

Provenance: helper lemma. IN-380, OP-19 campaign session 8, 2026-10-30. Self-contained helper for the strict-half acyclic-separation route. The general unrestricted one-child equality was refuted in IN-372; this work repairs only the strict-half existence reduction. Standard finite matching, rational density, and circulation weak duality are used. No new election bound or research novelty is claimed. See lean/AFTD/Scratch/In380Oct30/HalfThresholdDerivation.txt.

For any family C of subsets of a finite vertex set, if nonnegative real weights put every member of C strictly below half the total weight, nonnegative integer weights do so as well. The family may be arbitrary; finiteness and strictness are essential to this proof.
-/

open Finset
open scoped BigOperators
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000

theorem condorcet_finite_strict_separator_integer_weights
    (m : ℕ) (C : Finset (Fin m) → Prop)
    (w : Fin m → ℝ) (hw : ∀ a, 0 ≤ w a)
    (hsep : ∀ A, C A → 2 * (∑ a ∈ A, w a) < ∑ a, w a) :
    ∃ d : Fin m → ℕ, ∀ A, C A → 2 * (∑ a ∈ A, d a) < ∑ a, d a := by
  classical
  let K := {A : Finset (Fin m) // C A}
  let O : Set (Fin m → ℝ) := {x | ∀ A : K,
    2 * (∑ a ∈ A.val, max (x a) 0) < ∑ a, max (x a) 0}
  have hO : IsOpen O := by
    simp only [O,Set.ofPred_forall]
    apply isOpen_iInter_of_finite
    intro A
    apply isOpen_lt <;> fun_prop
  have hwO : w ∈ O := by
    intro A
    simpa only [max_eq_left (hw _)] using hsep A.val A.property
  have hdense : DenseRange (fun q : Fin m → ℚ => fun a => (q a : ℝ)) :=
    DenseRange.piMap (fun _ => Rat.denseRange_cast)
  obtain ⟨q,hq⟩ := hdense.exists_mem_open hO ⟨w,hwO⟩
  let u : Fin m → ℚ := fun a => max (q a) 0
  have hu : ∀ a, 0 ≤ u a := fun a => le_max_right _ _
  have huseq : ∀ A, C A → 2 * (∑ a ∈ A, u a) < ∑ a, u a := by
    intro A hA
    have h := hq ⟨A,hA⟩
    change 2 * (∑ a ∈ A, max (q a : ℝ) 0) < ∑ a, max (q a : ℝ) 0 at h
    exact_mod_cast h
  obtain ⟨D,d,hD,hd⟩ :=
    condorcet_half_cover_finite_nonnegative_rational_common_denominator u hu
  refine ⟨d,?_⟩
  intro A hA
  have h := mul_lt_mul_of_pos_left (huseq A hA) (show (0 : ℚ) < D by exact_mod_cast hD)
  have hDA : (D : ℚ) * (∑ a ∈ A, u a) = ∑ a ∈ A, (d a : ℚ) := by
    simp_rw [mul_sum,hd]
  have hDall : (D : ℚ) * (∑ a, u a) = ∑ a, (d a : ℚ) := by
    simp_rw [mul_sum,hd]
  have hleft : (D : ℚ) * (2 * ∑ a ∈ A, u a) = 2 * ∑ a ∈ A, (d a : ℚ) := by
    rw [← hDA]
    ring
  rw [hleft,hDall] at h
  exact_mod_cast h
