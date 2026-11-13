import AFTD.Prelude
import AFTD.Kb.Tcs.ForestGreedySignedStep
import AFTD.Kb.Tcs.ForestGreedyLawEnveloped
import AFTD.Kb.Tcs.ForestCarpoolTailEnvelope
import AFTD.Kb.Tcs.ForestGreedyHighTailStep
import AFTD.Kb.Tcs.ForestCarpoolFibonacciEnvelopeDecay

/-!
# forest_greedy_merge_large_levels

Topic: online_algorithms   Node: 277066486c36

Provenance: helper lemma. Helper for OP-1106, forest greedy carpooling; related background arXiv:2611.00388.

Two independent enveloped laws remain within the Fibonacci tail envelope after a greedy step at every integer level at least four.
-/

theorem forest_greedy_merge_large_levels
    (α β : Type) [Fintype α] [Fintype β] [Nonempty α] [Nonempty β]
    (X : α → ℤ) (Y : β → ℤ)
    (hX : forest_greedy_law_enveloped α X)
    (hY : forest_greedy_law_enveloped β Y) (D : ℕ) (hD : 4 ≤ D) :
    (((Finset.univ.filter (fun p : α × β × Bool =>
      (D : ℤ) ≤ forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2)).card : ℝ) /
        (Fintype.card (α × β × Bool) : ℝ)) ≤ forest_carpool_tail_envelope D := by
  have hd1 : 1 ≤ D := by omega
  have hdm : 1 ≤ D - 1 := by omega
  have hxp := hX.2.2 (D + 1) (by omega)
  have hxm := hX.2.2 (D - 1) hdm
  have hym := hY.2.2 (D - 1) hdm
  have he : 0 ≤ forest_carpool_tail_envelope (D - 1) := by
    unfold forest_carpool_tail_envelope
    split_ifs <;> positivity
  have hproduct :
      (((Finset.univ.filter (fun a => ((D - 1 : ℕ) : ℤ) ≤ X a)).card : ℝ) / Fintype.card α) *
      (((Finset.univ.filter (fun b => ((D - 1 : ℕ) : ℤ) ≤ Y b)).card : ℝ) / Fintype.card β) ≤
      forest_carpool_tail_envelope (D - 1) * forest_carpool_tail_envelope (D - 1) :=
    mul_le_mul hxm hym (by positivity) he
  have hstep := forest_greedy_high_tail_step α β X Y (D : ℤ)
  have hstep' :
    (((Finset.univ.filter (fun p : α × β × Bool =>
      (D : ℤ) ≤ forest_greedy_signed_step (X p.1) (Y p.2.1) p.2.2)).card : ℝ) /
        (Fintype.card (α × β × Bool) : ℝ)) ≤
      (((Finset.univ.filter (fun a => ((D + 1 : ℕ) : ℤ) ≤ X a)).card : ℝ) / Fintype.card α) +
      (((Finset.univ.filter (fun a => ((D - 1 : ℕ) : ℤ) ≤ X a)).card : ℝ) / Fintype.card α) *
      (((Finset.univ.filter (fun b => ((D - 1 : ℕ) : ℤ) ≤ Y b)).card : ℝ) / Fintype.card β) := by
    simpa only [Nat.cast_add, Nat.cast_one, Nat.cast_sub hd1] using hstep
  have hdecay := forest_carpool_fibonacci_envelope_decay D hD
  calc
    _ ≤ _ := hstep'
    _ ≤ forest_carpool_tail_envelope (D + 1) +
        forest_carpool_tail_envelope (D - 1) * forest_carpool_tail_envelope (D - 1) :=
      add_le_add hxp hproduct
    _ ≤ _ := by simpa [pow_two] using hdecay
