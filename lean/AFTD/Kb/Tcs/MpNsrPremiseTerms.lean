import AFTD.Prelude
import AFTD.Kb.Tcs.MpNsrPremise
import AFTD.Kb.Tcs.CnfLit
import AFTD.Kb.Tcs.CnfLitDecidableEq

/-!
# mp_nsr_premise_terms

Topic: proof_complexity   Node: de108be43f75

Provenance: formalization of a published result. Source: arXiv:2611.24548 Def 2.7

The pair of lists of left-hand side and right-hand side tropical terms (c : ℚ, m : CnfLit (Fin n) → ℕ) for an MP-NSR premise p : MpNsrPremise n F: clause C maps to ([(1, 0)], [(0, fun l => C.count l)]); weak_pos i to ([(0, 0)], [(0, fun l => if l = CnfLit.pos i then 1 else 0)]); weak_neg i to ([(0, 0)], [(0, fun l => if l = CnfLit.neg i then 1 else 0)]); pair_upper i to ([(1, 0)], [(0, fun l => if l = CnfLit.pos i ∨ l = CnfLit.neg i then 1 else 0)]); pair_lower i to ([(0, fun l => if l = CnfLit.pos i ∨ l = CnfLit.neg i then 1 else 0)], [(1, 0)]); resolution i to ([(0, fun l => if l = CnfLit.pos i then 1 else 0), (0, fun l => if l = CnfLit.neg i then 1 else 0)], [(0, 0)]).
-/

/-- Left-hand and right-hand tropical terms for each MP-NSR premise. -/
def mp_nsr_premise_terms (n : ℕ) (F : List (List (CnfLit (Fin n)))) (p : MpNsrPremise n F) : List (ℚ × (CnfLit (Fin n) → ℕ)) × List (ℚ × (CnfLit (Fin n) → ℕ)) := match p with
  | .clause C _ => ([(1, fun _ => 0)], [(0, fun l => C.count l)])
  | .weak_pos i => ([(0, fun _ => 0)], [(0, fun l => if l = CnfLit.pos i then 1 else 0)])
  | .weak_neg i => ([(0, fun _ => 0)], [(0, fun l => if l = CnfLit.neg i then 1 else 0)])
  | .pair_upper i => ([(1, fun _ => 0)], [(0, fun l => if l = CnfLit.pos i ∨ l = CnfLit.neg i then 1 else 0)])
  | .pair_lower i => ([(0, fun l => if l = CnfLit.pos i ∨ l = CnfLit.neg i then 1 else 0)], [(1, fun _ => 0)])
  | .resolution i =>
      ([(0, fun l => if l = CnfLit.pos i then 1 else 0),
        (0, fun l => if l = CnfLit.neg i then 1 else 0)],
       [(0, fun _ => 0)])
