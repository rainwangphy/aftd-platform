import AFTD.Prelude

/-!
# IsClosestCandidate

Topic: mechanism_design   Node: 4638d65b5989

Provenance: helper lemma. helper notion for the closest candidate location t(i) of arXiv:2610.18006 (Truthful two-facility location with candidate locations in metric spaces), Sec. 2

c ∈ C and d(y, c) ≤ d(y, c') for every c' ∈ C.
-/

/-- `c` is a closest point of the finite set `C` to `y` (ties allowed). -/
def IsClosestCandidate {X : Type*} [MetricSpace X] (C : Finset X) (y c : X) : Prop :=
  c ∈ C ∧ ∀ c' ∈ C, dist y c ≤ dist y c'
