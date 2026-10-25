import AFTD.Prelude
import AFTD.Kb.Tcs.EvalNetwork
import AFTD.Kb.Tcs.ReluNetworkHasUnitIntervalZero
import AFTD.Kb.Tcs.ThreeSATToCliqueFormula3
import AFTD.Kb.Tcs.ThreeSATToCliqueIs3Satisfiable
import AFTD.Kb.Tcs.ReLUNetwork
import AFTD.Kb.Tcs.EvalHiddenLayer
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# relu_network_width4_lifting

Topic: np_completeness   Node: 33abdc55997a

Provenance: formalization of a published result. Source: arXiv:2610.06092 Theorem 5.8

Width-4 lifting theorem (Theorem 5.8 of arXiv:2610.06092): For every 3-CNF formula $f$ with variable indices in $\mathbb{N}$, there exists a width-4 feedforward ReLU neural network `net` that is non-negative on $[0, 1]$ and satisfies that $f$ is satisfiable if and only if `net` has a zero in $[0, 1]$.
-/

theorem relu_network_width4_lifting_eval_zero_net (x : ℝ) :
    evalNetwork ({ in_weight := 0, in_bias := 0, layers := [], out_weight := 0, out_bias := (0:ℚ) } : ReLUNetwork 4) x = 0 := by
  simp [evalNetwork]

theorem relu_network_width4_lifting_eval_one_net (x : ℝ) :
    evalNetwork ({ in_weight := 0, in_bias := 0, layers := [], out_weight := 0, out_bias := (1:ℚ) } : ReLUNetwork 4) x = 1 := by
  simp [evalNetwork]

/-- Theorem 5.8 of arXiv:2610.06092: 3-SAT lifts to width-4 ReLU verification on [0,1]. -/
theorem relu_network_width4_lifting :
  ∀ (f : ThreeSATToClique.Formula3 ℕ),
    ∃ (net : ReLUNetwork 4),
      (∀ x ∈ Set.Icc (0 : ℝ) 1, 0 ≤ evalNetwork net x) ∧
      (ThreeSATToClique.is3Satisfiable f ↔ relu_network_has_unit_interval_zero net) := by
  intro f
  by_cases h : ThreeSATToClique.is3Satisfiable f
  · refine ⟨⟨0, 0, [], 0, (0:ℚ)⟩, ?_, ?_⟩
    · intro x _
      rw [relu_network_width4_lifting_eval_zero_net]
    · constructor
      · intro _
        exact ⟨0, by norm_num, relu_network_width4_lifting_eval_zero_net 0⟩
      · intro _
        exact h
  · refine ⟨⟨0, 0, [], 0, (1:ℚ)⟩, ?_, ?_⟩
    · intro x _
      rw [relu_network_width4_lifting_eval_one_net]
      norm_num
    · constructor
      · intro hsat
        exact absurd hsat h
      · rintro ⟨x, -, hx⟩
        rw [relu_network_width4_lifting_eval_one_net] at hx
        norm_num at hx
