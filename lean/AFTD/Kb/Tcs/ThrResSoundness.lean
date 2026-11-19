import AFTD.Prelude
import AFTD.Kb.Tcs.ThrResDerivable
import AFTD.Kb.Tcs.EvalThrLits
import AFTD.Kb.Tcs.EvalCnfLit
import AFTD.Kb.GameTheoryEconomics.LinearOrderToTotalPreorder
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.CnfLitCompl
import AFTD.Kb.GameTheoryEconomics.TotalPreorder

/-!
# thr_res_soundness

Topic: proof_complexity   Node: d12ea3b947fc

Provenance: formalization of a published result. Source: arXiv:2611.24548 Theorem 2.18

Soundness of Threshold Resolution: for any CNF formula F : List (List (CnfLit V)), multiset of literals f : Multiset (CnfLit V), and integer s : ℤ, if ThrResDerivable F f s holds, then for every Boolean assignment α : V → Bool satisfying F (meaning that for every clause C ∈ F there is some literal l ∈ C such that eval_cnf_lit α l = true), the threshold condition holds: s ≤ (eval_thr_lits α f : ℤ).
-/

theorem thr_res_soundness_eval_add {V : Type*} (α : V → Bool) (f₁ f₂ : Multiset (CnfLit V)) :
    eval_thr_lits α (f₁ + f₂) = eval_thr_lits α f₁ + eval_thr_lits α f₂ := by
  change (Multiset.filter (fun l => eval_cnf_lit α l = true) (f₁ + f₂)).card =
    (Multiset.filter (fun l => eval_cnf_lit α l = true) f₁).card +
    (Multiset.filter (fun l => eval_cnf_lit α l = true) f₂).card
  rw [Multiset.filter_add, Multiset.card_add]

theorem thr_res_soundness_eval_zero {V : Type*} (α : V → Bool) :
    eval_thr_lits α 0 = 0 := by
  change (Multiset.filter (fun l => eval_cnf_lit α l = true) 0).card = 0
  simp

theorem thr_res_soundness_eval_cnf_lit_compl {V : Type*} (α : V → Bool) (l : CnfLit V) :
    eval_cnf_lit α (cnf_lit_compl l) = !eval_cnf_lit α l := by
  cases l <;> simp [eval_cnf_lit, cnf_lit_compl]

theorem thr_res_soundness_eval_cons {V : Type*} (α : V → Bool) (l : CnfLit V) (f : Multiset (CnfLit V)) :
    eval_thr_lits α (l ::ₘ f) = (if eval_cnf_lit α l = true then 1 else 0) + eval_thr_lits α f := by
  change (Multiset.filter (fun x => eval_cnf_lit α x = true) (l ::ₘ f)).card =
    (if eval_cnf_lit α l = true then 1 else 0) + (Multiset.filter (fun x => eval_cnf_lit α x = true) f).card
  rw [Multiset.filter_cons, Multiset.card_add]
  split_ifs with h
  · simp
  · simp

theorem thr_res_soundness_eval_compl_pair {V : Type*} (α : V → Bool) (l : CnfLit V) :
    eval_thr_lits α (l ::ₘ cnf_lit_compl l ::ₘ 0) = 1 := by
  rw [thr_res_soundness_eval_cons, thr_res_soundness_eval_cons, thr_res_soundness_eval_zero, thr_res_soundness_eval_cnf_lit_compl]
  cases eval_cnf_lit α l <;> rfl

theorem thr_res_soundness_eval_coe_list_pos {V : Type*} (α : V → Bool) (C : List (CnfLit V))
    (hl : ∃ l ∈ C, eval_cnf_lit α l = true) :
    1 ≤ eval_thr_lits α (↑C : Multiset (CnfLit V)) := by
  rcases hl with ⟨l, hin, heval⟩
  change 1 ≤ (Multiset.filter (fun x => eval_cnf_lit α x = true) (↑C : Multiset (CnfLit V))).card
  have hmem : l ∈ Multiset.filter (fun x => eval_cnf_lit α x = true) (↑C : Multiset (CnfLit V)) := by
    rw [Multiset.mem_filter]
    exact ⟨Multiset.mem_coe.mpr hin, heval⟩
  have hpos : 0 < (Multiset.filter (fun x => eval_cnf_lit α x = true) (↑C : Multiset (CnfLit V))).card :=
    Multiset.card_pos_iff_exists_mem.mpr ⟨l, hmem⟩
  omega

theorem thr_res_soundness_eval_pos_of_false {V : Type*} (α : V → Bool) (x : V) (h : α x = false) :
    eval_thr_lits α {CnfLit.pos x} = 0 := by
  have : ({CnfLit.pos x} : Multiset (CnfLit V)) = CnfLit.pos x ::ₘ 0 := rfl
  rw [this, thr_res_soundness_eval_cons, thr_res_soundness_eval_zero, add_zero]
  simp [eval_cnf_lit, h]

theorem thr_res_soundness_eval_neg_of_true {V : Type*} (α : V → Bool) (x : V) (h : α x = true) :
    eval_thr_lits α {CnfLit.neg x} = 0 := by
  have : ({CnfLit.neg x} : Multiset (CnfLit V)) = CnfLit.neg x ::ₘ 0 := rfl
  rw [this, thr_res_soundness_eval_cons, thr_res_soundness_eval_zero, add_zero]
  simp [eval_cnf_lit, h]

/-- Theorem 2.18 (Soundness): Every line of a Thr-Res derivation is satisfied by every assignment satisfying the CNF. -/
theorem thr_res_soundness {V : Type*} (F : List (List (CnfLit V))) (f : Multiset (CnfLit V)) (s : ℤ) (hderiv : ThrResDerivable F f s) (α : V → Bool) (hα : ∀ C ∈ F, ∃ l ∈ C, eval_cnf_lit α l = true) : s ≤ (eval_thr_lits α f : ℤ) := by
  induction hderiv with
  | source =>
    rw [thr_res_soundness_eval_zero]
    rfl
  | @clause f s C h hin ih =>
    rw [thr_res_soundness_eval_add]
    push_cast
    have hc := thr_res_soundness_eval_coe_list_pos α C (hα C hin)
    omega
  | @resolution f s x h1 h2 ih1 ih2 =>
    cases hx : α x with
    | true =>
      rw [thr_res_soundness_eval_add, thr_res_soundness_eval_neg_of_true α x hx, add_zero] at ih2
      exact ih2
    | false =>
      rw [thr_res_soundness_eval_add, thr_res_soundness_eval_pos_of_false α x hx, add_zero] at ih1
      exact ih1
  | weak h ih =>
    rw [thr_res_soundness_eval_add]
    push_cast
    omega
  | introduce h ih =>
    rw [thr_res_soundness_eval_add, thr_res_soundness_eval_compl_pair]
    push_cast
    omega
  | simplify h ih =>
    rw [thr_res_soundness_eval_add, thr_res_soundness_eval_compl_pair] at ih
    push_cast at ih
    omega
