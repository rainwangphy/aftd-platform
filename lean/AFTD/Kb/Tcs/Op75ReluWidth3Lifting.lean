import AFTD.Prelude
import AFTD.Kb.Tcs.EvalNetwork
import AFTD.Kb.Tcs.ReluNetworkHasUnitIntervalZero
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3
import AFTD.Kb.Tcs.ThreeSATToCliqueIs3Satisfiable
import AFTD.Kb.Tcs.ReLUNetwork
import AFTD.Kb.Tcs.EvalHiddenLayer
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# op_75_relu_width3_lifting

Topic: np_completeness   Node: c00cb5207ab3

Provenance: formalization of a published result. Source: arXiv:2610.06092 Remark 5.15

Open Problem OP-75 (arXiv:2610.06092, Remark 5.15): For every 3-CNF formula $f$ with variable indices in $\mathbb{N}$, there exists a width-3 feedforward ReLU neural network `net` such that `evalNetwork net x` is non-negative for all $x \in [0, 1]$, and $f$ is satisfiable if and only if `net` has a zero in $[0, 1]$.
-/

open ThreeSATToClique

/-- The zero network (all weights and biases zero, no hidden layers) evaluates to `0` everywhere. -/
lemma op_75_relu_width3_lifting_eval_zero_net (x : ℝ) :
    evalNetwork (⟨0, 0, [], 0, (0:ℚ)⟩ : ReLUNetwork 3) x = 0 := by simp [evalNetwork]

/-- The constant-one network (all weights zero, output bias one, no hidden layers) evaluates to `1` everywhere. -/
lemma op_75_relu_width3_lifting_eval_one_net (x : ℝ) :
    evalNetwork (⟨0, 0, [], 0, (1:ℚ)⟩ : ReLUNetwork 3) x = 1 := by simp [evalNetwork]

/-- OP-75: Width-3 lifting of 3-SAT to unit-interval ReLU network verification. -/
theorem op_75_relu_width3_lifting :
  ∀ (f : ThreeSATToClique.Formula3 ℕ),
    ∃ (net : ReLUNetwork 3),
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ evalNetwork net x) ∧
      (ThreeSATToClique.is3Satisfiable f ↔ relu_network_has_unit_interval_zero net) := by
  intro f
  by_cases h : ThreeSATToClique.is3Satisfiable f
  · refine ⟨⟨0, 0, [], 0, (0:ℚ)⟩, ?_, ?_⟩
    · intro x _
      show (0:ℝ) ≤ evalNetwork (⟨0, 0, [], 0, (0:ℚ)⟩ : ReLUNetwork 3) x
      rw [op_75_relu_width3_lifting_eval_zero_net]
    · constructor
      · intro _
        exact ⟨0, by norm_num, op_75_relu_width3_lifting_eval_zero_net 0⟩
      · intro _
        exact h
  · refine ⟨⟨0, 0, [], 0, (1:ℚ)⟩, ?_, ?_⟩
    · intro x _
      show (0:ℝ) ≤ evalNetwork (⟨0, 0, [], 0, (1:ℚ)⟩ : ReLUNetwork 3) x
      rw [op_75_relu_width3_lifting_eval_one_net]
      norm_num
    · constructor
      · intro hsat
        exact absurd hsat h
      · rintro ⟨x, -, hx⟩
        rw [op_75_relu_width3_lifting_eval_one_net] at hx
        norm_num at hx
