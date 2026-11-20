import AFTD.Prelude
import AFTD.Kb.Tcs.ThrResDerivable
import AFTD.Kb.Tcs.ThrResSoundness
import AFTD.Kb.Tcs.CnfSatisfiable
import AFTD.Kb.Tcs.EvalCnfLit
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.EvalThrLits

/-!
# thr_res_unsat_of_refutation

Topic: proof_complexity   Node: d7f5f81bef31

Provenance: formalization of a published result. Source: arXiv:2611.24548 Theorem 2.18

If a Threshold Resolution refutation of a CNF formula F : List (List (CnfLit V)) exists (namely ThrResDerivable F 0 1), then F is unsatisfiable (¬ CnfSatisfiable F).
-/

/-- Soundness for refutations: if a Thr-Res refutation exists, the CNF formula is unsatisfiable. -/
theorem thr_res_unsat_of_refutation {V : Type*} (F : List (List (CnfLit V))) (href : ThrResDerivable F 0 1) : ¬ CnfSatisfiable F := by
  intro hsat
  obtain ⟨α, hα⟩ := hsat
  have hα' : ∀ C ∈ F, ∃ l ∈ C, eval_cnf_lit α l = true := by
    intro C hC
    obtain ⟨l, hl, hlt⟩ := hα C hC
    refine ⟨l, hl, ?_⟩
    match l with
    | CnfLit.pos v => simpa [eval_cnf_lit] using hlt
    | CnfLit.neg v => cases hv : α v <;> simp_all [eval_cnf_lit]
  have h := thr_res_soundness F 0 1 href α hα'
  simp only [eval_thr_lits, Multiset.filter_zero, Multiset.card_zero] at h
  omega
