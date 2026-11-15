import AFTD.Prelude
import AFTD.Kb.Tcs.Op75Tm2OutputLinearBound

/-!
# op75_tm2_poly_output_size

Topic: np_completeness   Node: 4ac776163fcb

Provenance: helper lemma. OP-75: polynomial output-size bound needed for composing Karp reductions.

Every function computed by a polynomial-time TM2 has output encoding length bounded by a polynomial in its input encoding length.
-/

theorem op75_tm2_poly_output_size {α β αΓ βΓ : Type} {ea : α → List αΓ} {eb : β → List βΓ} {f : α → β} (M : Turing.TM2ComputableInPolyTime ea eb f) : ∃ q : Polynomial ℕ, ∀ a, (eb (f a)).length ≤ q.eval (ea a).length := by
  obtain ⟨C, hC⟩ := op75_tm2_output_linear_bound M.tm
  refine ⟨Polynomial.X + Polynomial.C C * M.time, ?_⟩
  intro a
  have h := hC (List.map M.inputAlphabet.invFun (ea a))
    (List.map M.outputAlphabet.invFun (eb (f a))) (M.time.eval (ea a).length)
    ⟨M.outputsFun a⟩
  simpa using h
