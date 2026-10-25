import AFTD.Prelude
import AFTD.Kb.Tcs.EvalNetwork
import AFTD.Kb.Tcs.Relu
import AFTD.Kb.Tcs.ReLUNetwork
import AFTD.Kb.Tcs.EvalHiddenLayer
import AFTD.Kb.Tcs.ReLUHiddenLayer

/-!
# relu_network_eval_continuous

Topic: np_completeness   Node: bef0aec4deb4

Provenance: helper lemma. arXiv:2610.06092 Section 2.1

For every natural number $k$ and every feedforward ReLU neural network `net` of width $k$ with rational weights and biases, the evaluation function `evalNetwork net : ℝ → ℝ` is continuous.
-/

/-- Continuity of feedforward ReLU neural network evaluation. -/
theorem relu_network_eval_continuous {k : ℕ} (net : ReLUNetwork k) :
  Continuous (evalNetwork net) := by
  have hrelu : Continuous relu := by
    unfold relu
    simpa using (continuous_id.max continuous_const : Continuous fun x : ℝ => max x 0)
  have hlayer : ∀ (l : ReLUHiddenLayer k) (i : Fin k),
      Continuous fun v : Fin k → ℝ => evalHiddenLayer l v i := by
    intro l i
    unfold evalHiddenLayer
    exact hrelu.comp (by continuity)
  have hlayer_full : ∀ l : ReLUHiddenLayer k,
      Continuous fun v : Fin k → ℝ => evalHiddenLayer l v := by
    intro l
    exact continuous_pi (hlayer l)
  have hfold : ∀ (layers : List (ReLUHiddenLayer k)) (f : ℝ → Fin k → ℝ),
      Continuous f →
      Continuous fun x => List.foldl (fun v l => evalHiddenLayer l v) (f x) layers := by
    intro layers
    induction layers with
    | nil => intro f hf; simpa using hf
    | cons l ls ih =>
      intro f hf
      simp only [List.foldl_cons]
      have hc : Continuous fun x => evalHiddenLayer l (f x) := (hlayer_full l).comp hf
      exact ih (fun x => evalHiddenLayer l (f x)) hc
  have hinit : Continuous fun x : ℝ => fun i : Fin k => (net.in_weight i : ℝ) * x + (net.in_bias i : ℝ) := by
    apply continuous_pi
    intro i
    exact (continuous_const.mul continuous_id).add continuous_const
  have hhidden := hfold net.layers _ hinit
  unfold evalNetwork
  have hsum : Continuous fun x : ℝ =>
      ∑ i, (net.out_weight i : ℝ) * (List.foldl (fun v l => evalHiddenLayer l v)
        (fun i => (net.in_weight i : ℝ) * x + (net.in_bias i : ℝ)) net.layers) i := by
    apply continuous_finsetSum
    intro i _
    exact continuous_const.mul ((continuous_apply i).comp hhidden)
  exact hsum.add continuous_const
