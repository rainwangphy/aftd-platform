import AFTD.Prelude
import AFTD.Kb.GameTheoryEconomics.IsClosestCandidate

/-!
# IsFixedDictatorOutput

Topic: mechanism_design   Node: d069480366aa

Provenance: formalization of a published result. Source: arXiv:2610.18006 (Truthful two-facility location with candidate locations in metric spaces), Sec. 4.1, Mechanism 2 (Fixed-Dictator). Lean differs: the fixed agents and the tie-breaking order are arbitrary (the predicate allows every choice), so results about it hold for every fixed choice

w is an outcome of Fixed-Dictator (Mechanism 2 of arXiv:2610.18006) for some fixed agents and some tie-breaking, the three cases being: a doubleton agent exists; no doubleton agent but both facilities approved; only one facility approved.
-/

/-- `w` is an output of the Fixed-Dictator mechanism (Mechanism 2), for some choice of the fixed agents and any tie-breaking: (1) if some agent approves both facilities, `w 0` is a closest candidate to such an agent `i` and `w 1` a closest candidate to `i` among the others (her two closest locations); (2) otherwise, if both facilities are approved, `w 0` is closest to a fixed agent `i` approving `F₁` and `w 1` is closest to a fixed agent `j` approving `F₂` among the candidates other than `w 0` (her closest available location); (3) otherwise only `F_k` is approved, `w k` is closest to a fixed agent `i` approving it and `w (1 - k)` is her second-closest. -/
def IsFixedDictatorOutput {ι X : Type*} [MetricSpace X] [DecidableEq X] (C : Finset X) (x : ι → X)
    (p : ι → Fin 2 → Bool) (w : Fin 2 → X) : Prop :=
  (∃ i, p i 0 ∧ p i 1 ∧ IsClosestCandidate C (x i) (w 0) ∧
      IsClosestCandidate (C.erase (w 0)) (x i) (w 1)) ∨
  ((∀ a, ¬ (p a 0 ∧ p a 1)) ∧ ∃ i j, p i 0 ∧ p j 1 ∧ IsClosestCandidate C (x i) (w 0) ∧
      IsClosestCandidate (C.erase (w 0)) (x j) (w 1)) ∨
  (∃ k : Fin 2, (∀ a, p a (1 - k) = false) ∧ ∃ i, p i k ∧ IsClosestCandidate C (x i) (w k) ∧
      IsClosestCandidate (C.erase (w k)) (x i) (w (1 - k)))
