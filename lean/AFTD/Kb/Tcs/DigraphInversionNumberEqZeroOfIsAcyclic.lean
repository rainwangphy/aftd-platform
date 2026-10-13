import AFTD.Prelude
import AFTD.Kb.Tcs.DigraphInversionNumber
import AFTD.Kb.Tcs.DigraphIsAcyclic
import AFTD.Kb.Tcs.DigraphInvert

/-!
# digraph_inversion_number_eq_zero_of_is_acyclic

Topic: graphs   Node: 74d303a20a4c

Provenance: helper lemma. Sanity lemma for digraph_inversion_number (arXiv:2610.13798, Sec. 1).

An acyclic digraph has inversion number 0.
-/

theorem digraph_inversion_number_eq_zero_of_is_acyclic {V : Type*} (D : Digraph V)
    (h : digraph_is_acyclic D) : digraph_inversion_number D = 0 := by
  apply Nat.sInf_eq_zero.mpr
  left
  exact ⟨[], rfl, h⟩
