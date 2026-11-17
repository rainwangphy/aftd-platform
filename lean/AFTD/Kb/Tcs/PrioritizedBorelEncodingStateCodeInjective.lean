import AFTD.Prelude
import AFTD.Kb.Tcs.Enc1385Game

/-!
# prioritized_borel_encoding_state_code_injective

Topic: automata   Node: f1692825013e

Provenance: helper lemma. Phase-state encoding for arXiv:2611.10136, Conjecture 19.

Distinct states have distinct one-hot bit codes.
-/

theorem prioritized_borel_encoding_state_code_injective {Q : Type} [Fintype Q] : Function.Injective (@enc1385StateCode Q _) := by
  classical
  intro q r h
  apply (Fintype.equivFin Q).injective
  have hf : (fun i : Fin (Fintype.card Q) => decide (i = Fintype.equivFin Q q)) =
      (fun i : Fin (Fintype.card Q) => decide (i = Fintype.equivFin Q r)) := by
    apply List.ofFn_injective
    simpa [enc1385StateCode] using h
  have he := congrFun hf (Fintype.equivFin Q q)
  simpa using he
