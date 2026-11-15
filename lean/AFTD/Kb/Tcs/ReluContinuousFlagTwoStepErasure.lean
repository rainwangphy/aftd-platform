import AFTD.Prelude

/-!
# relu_continuous_flag_two_step_erasure

Topic: np_completeness   Node: cbd85f59218f

Provenance: helper lemma. Intermediate-value obstruction for the clause-flag approach to OP-75, arXiv:2610.06092, Remark 5.15; this concerns a general class of candidate updates, not the open problem itself.

Suppose a real-valued flag update G is continuous in its test input at an initial flag p, with G(0,p)=p and G(1,p)=p-c, and a true test clears the flag c: G(1,c)=0. If c<p≤2c, there is an intermediate test value e in [0,1] for which applying the e test and then the true test clears the flag to zero.
-/

theorem relu_continuous_flag_two_step_erasure (G : ℝ → ℝ → ℝ) (c p : ℝ) (hp : c < p) (hp2 : p ≤ 2 * c) (hcont : ContinuousOn (fun e => G e p) (Set.Icc 0 1)) (hzero : G 0 p = p) (hone : G 1 p = p - c) (hclear : G 1 c = 0) : ∃ e ∈ Set.Icc (0 : ℝ) 1, G 1 (G e p) = 0 := by
  have hmem : c ∈ Set.Icc ((fun e => G e p) 1) ((fun e => G e p) 0) := by
    simp only [hone, hzero, Set.mem_Icc]
    constructor <;> linarith
  obtain ⟨e, he, heq⟩ := intermediate_value_Icc' (by norm_num : (0 : ℝ) ≤ 1) hcont hmem
  change G e p = c at heq
  exact ⟨e, he, by rw [heq, hclear]⟩
