import AFTD.Prelude

/-!
# uniform_kserver_det_schedule

Topic: online_algorithms   Node: ee8034255fd9

Provenance: formalization of a published result. Source: arXiv:2610.37192 Sec. 6

Given types α and β, a mapping A : List α → β, and an input list ρ : List α, uniform_kserver_det_schedule A ρ is the list of elements of β of length ρ.length whose t-th element (for 0 ≤ t < ρ.length) is A (ρ.take (t + 1)).
-/

/-- The schedule of outputs chosen online by A on input sequence ρ. -/
def uniform_kserver_det_schedule {α β : Type*}
    (A : List α → β) (ρ : List α) : List β :=
  (List.range ρ.length).map (fun t => A (ρ.take (t + 1)))
