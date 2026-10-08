import AFTD.Prelude
import AFTD.Kb.Tcs.HalvingLogSuccLeLogOfDoubleLe
import AFTD.Kb.Tcs.HalvingMistakeHalves
import AFTD.Kb.Tcs.HalvingMistakes
import AFTD.Kb.Tcs.HalvingPredict
import AFTD.Kb.Tcs.HalvingTargetMemUpdate
import AFTD.Kb.Tcs.HalvingUpdate
import AFTD.Kb.Tcs.HalvingUpdateSubset
import AFTD.Kb.Tcs.V

/-!
# Halving.mistakes_bound

Topic: learning   Node: 0bdf9bb6eef2

Provenance: helper lemma. TCSlib, `Halving.mistakes_bound`. Lean proof by Arhaan Aggarwal, from https://github.com/Shilun-Allan-Li/tcslib/blob/c8a02591b1e51faa8cb90dd30cfe2d6a2d5032ea/TCSlib/LearningTheory/MistakeBounds/Halving.lean (Copyright (c) 2026 Arhaan Aggarwal. All rights reserved, Apache-2.0); 1 verbatim; compiled here.

Mistake bound for the Halving Algorithm. Let $\mathtt{eval} : \mathit{Hyp} \to X \to \mathsf{Bool}$ be an evaluation map, let $V$
be a finite version space of hypotheses, and fix a target hypothesis $\mathtt{target}
\in V$ whose predictions supply the true label at each step. Then for every input
sequence $xs$, the total number of mistakes made by the Halving Algorithm — which
predicts by majority vote over the current version space and, after each input, retains
only those hypotheses that agreed with the observed label — satisfies
\[
\mathtt{mistakes}(\mathtt{eval}, \mathtt{target}, V, xs) \;\le\; \lfloor \log_2 \abs{V}
\rfloor.
\]
-/

set_option relaxedAutoImplicit false in
set_option autoImplicit false in
variable {Hyp X : Type*} in
/-- In the realizable setting, the Halving Algorithm makes at most `⌊log₂ |V|⌋` mistakes: if the target hypothesis lies in the finite version space `V`, then on any finite list of inputs `xs`, labelled by `target`, the number of mistakes is at most `Nat.log 2 V.card`. [MRT18, Thm 8.1]; origin [Lit88, §3]. Deviation: the bound is stated as `Nat.log 2 V.card` (the floor of `log₂ |V|`) over an explicit finite list of examples with an explicit realizable target `target ∈ V`; the source's `opt(H) ≤ log₂ |H|` is the same bound for the adversarial online model. **Proof sketch.** Induction on the list of inputs, generalizing the version space `V`. The empty list makes no mistakes. For an input `x` followed by `xs`, let `y` be the target's label on `x` and `V'` the version space updated on `(x, y)`. Step 1: the target survives the update (`target ∈ V'`), so the induction hypothesis applies to `V'` and bounds the mistakes on `xs` by `⌊log₂ |V'|⌋`. Step 2 (no mistake on `x`): `V' ⊆ V`, so `|V'| ≤ |V|` and, by monotonicity of `Nat.log`, `⌊log₂ |V'|⌋ ≤ ⌊log₂ |V|⌋`; the mistake count on `x :: xs` equals that on `xs`. Step 3 (mistake on `x`): by the halving lemma `2 · |V'| ≤ |V|`, and `V'` is nonempty because it contains the target, so `⌊log₂ |V'|⌋ + 1 ≤ ⌊log₂ |V|⌋`; the one mistake on `x` is paid by this unit of logarithmic budget. -/
theorem Halving.mistakes_bound
    (eval : Hyp → X → Bool) (target : Hyp) (V : Finset Hyp) (xs : List X)
    (htarget : target ∈ V) :
    mistakes eval target V xs ≤ Nat.log 2 V.card := by
  induction xs generalizing V with
  | nil =>
      simp [mistakes]
  | cons x xs ih =>
      let y := eval target x
      let V' := update eval V x y
      -- Step 1: the target survives the update, so the induction hypothesis applies to `V'`.
      have htarget' : target ∈ V' := by
        simpa [V', y] using target_mem_update eval target V x htarget
      have ih' : mistakes eval target V' xs ≤ Nat.log 2 V'.card :=
        ih V' htarget'
      by_cases hcorr : predict eval V x = y
      · -- No mistake: the version space can only shrink.
        -- Step 2: `V' ⊆ V`, hence `|V'| ≤ |V|` and the log bound is monotone.
        have hsubset : V' ⊆ V := by
          simpa [V', y] using update_subset eval V x y
        have hcard : V'.card ≤ V.card := Finset.card_le_card hsubset
        have hlog : Nat.log 2 V'.card ≤ Nat.log 2 V.card :=
          Nat.log_mono_right hcard
        calc
          mistakes eval target V (x :: xs)
              = mistakes eval target V' xs := by
                  simp [mistakes, y, V', hcorr]
          _ ≤ Nat.log 2 V'.card := ih'
          _ ≤ Nat.log 2 V.card := hlog
      · -- Mistake: apply the halving lemma and spend one unit of logarithmic budget.
        -- Step 3: `2·|V'| ≤ |V|` and `V'` is nonempty, so `⌊log₂ |V'|⌋ + 1 ≤ ⌊log₂ |V|⌋`.
        have hhalve : 2 * V'.card ≤ V.card := by
          simpa [V', y] using mistake_halves eval V x y hcorr
        have hpos : 0 < V'.card := by
          exact Finset.card_pos.mpr ⟨target, htarget'⟩
        have hlogstep : Nat.log 2 V'.card + 1 ≤ Nat.log 2 V.card :=
          log_succ_le_log_of_double_le hpos hhalve
        calc
          mistakes eval target V (x :: xs)
              = 1 + mistakes eval target V' xs := by
                  simp [mistakes, y, V', hcorr]
          _ ≤ 1 + Nat.log 2 V'.card := Nat.add_le_add_left ih' 1
          _ = Nat.log 2 V'.card + 1 := by omega
          _ ≤ Nat.log 2 V.card := hlogstep
