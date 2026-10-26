import AFTD.Prelude
import AFTD.Kb.Tcs.AdaptivePolicy

/-!
# IsPartiallyAdaptive

Topic: online_algorithms   Node: e68e4cc55cbe

Provenance: formalization of a published result. Source: arXiv:2610.13775, Sec. 2.1

A search policy `π : AdaptivePolicy n` for Pandora's problem is partially adaptive if there exists a predetermined ordered list of boxes `order` such that along every execution branch, the sequence of boxes opened is a prefix of `order`.
-/

/-- A policy is partially adaptive if its opened boxes along every branch form a prefix of a fixed box order. -/
def IsPartiallyAdaptive {n : ℕ} (π : AdaptivePolicy n) : Prop := ∃ order : List (Fin n), aux order π
where
  aux : List (Fin n) → AdaptivePolicy n → Prop
    | _, .stop => True
    | [], .openBox _ _ => False
    | b :: rest, .openBox b' cont => b' = b ∧ ∀ v, aux rest (cont v)
