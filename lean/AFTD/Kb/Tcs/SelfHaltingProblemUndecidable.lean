import AFTD.Prelude

/-!
# self_halting_problem_undecidable

Topic: computability   Node: 829d21ca55f9

Provenance: formalization of a published result. Source: standard textbook result (computability theory: undecidability of the halting problem, diagonal form)

The diagonal halting problem is not computable.
-/

/-- The diagonal halting problem is undecidable (not computable). -/
theorem self_halting_problem_undecidable : ¬ComputablePred (fun c : Nat.Partrec.Code => (Nat.Partrec.Code.eval c (Encodable.encode c)).Dom) := by
  intro h
  obtain ⟨_, hc⟩ := h
  let f : Nat.Partrec.Code → ℕ →. ℕ := fun c _ =>
    cond (decide (Nat.Partrec.Code.eval c (Encodable.encode c)).Dom) Part.none (Part.some 0)
  have hf : Partrec₂ f :=
    Partrec.cond (hc.comp Computable.fst) Partrec.none (Computable.const 0).partrec
  obtain ⟨c, e⟩ := Nat.Partrec.Code.fixed_point₂ hf
  have e_app := congr_fun e (Encodable.encode c)
  dsimp [f] at e_app
  by_cases H : (Nat.Partrec.Code.eval c (Encodable.encode c)).Dom
  · have h_none := e_app ▸ H
    simp [H] at h_none
  · apply H
    rw [e_app]
    simp [H]
