import AFTD.Prelude
import AFTD.Kb.Tcs.PandoraDeadlineInstance
import AFTD.Kb.Tcs.AdaptivePolicy
import AFTD.Kb.Tcs.DiscreteDist

/-!
# expectedUtilityDUS

Topic: online_algorithms   Node: b297c20a1d58

Provenance: formalization of a published result. Source: arXiv:2610.13775 Sec. 2.1

The expected net utility of an adaptive policy `π : AdaptivePolicy inst.n` under deferred-until-stopping commitment on a Pandora's problem instance with deadlines `inst : PandoraDeadlineInstance`. Evaluated recursively starting with an empty history: upon opening a box `b`, the box cost `inst.cost b` is subtracted and the expectation over the realized values `v` in the support of `(inst.dist b)` of continuing with `(b, v) :: history` is taken; upon stopping, the policy receives the maximum realized value among all opened boxes in the history (or 0 if empty).
-/

/-- Expected net utility of an adaptive policy under deferred-until-stopping commitment in Pandora's problem with deadlines. -/
noncomputable def expectedUtilityDUS (inst : PandoraDeadlineInstance) (π : AdaptivePolicy inst.n) : ℝ := aux [] π
where
  aux (history : List (Fin inst.n × ℝ)) : AdaptivePolicy inst.n → ℝ
    | .stop =>
        history.foldl (fun acc bv => max acc bv.2) 0
    | .openBox b cont =>
        (∑ v ∈ (inst.dist b).support,
          (inst.dist b).prob v * aux ((b, v) :: history) (cont v)) -
        inst.cost b
