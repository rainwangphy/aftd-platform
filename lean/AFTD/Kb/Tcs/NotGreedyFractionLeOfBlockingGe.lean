import AFTD.Prelude
import AFTD.Kb.Tcs.IsHereditarySegmentProperty
import AFTD.Kb.Tcs.GreedyMatching
import AFTD.Kb.Tcs.PointsInGeneralPosition
import AFTD.Kb.Tcs.SegmentBlockingNumber
import AFTD.Kb.Tcs.GreedyStep

/-!
# not_greedy_fraction_le_of_blocking_ge

Topic: online_algorithms   Node: 837e1516ad47

Provenance: original. Related work: refutes `greedy_fraction_le_of_blocking_ge`

The statement `greedy_fraction_le_of_blocking_ge` is false: The statement is false as written; a machine-checked refutation is provided.

Counterexample: take P := fun t => t = ∅ (so P holds only on the empty family), ℓ = 1, p = 0.

* P is hereditary: P ∅ holds, and if s ⊆ t with P t (i.e. t = ∅) then s = ∅, so P s.
* The hypothesis hβ : p ≤ segment_blocking_number P 1 is `0 ≤ _`, hence trivial — in fact the set {p' | ∃ L S, L.card = 1 ∧ P L ∧ ...} is empty (L.card = 1 with L = ∅ is impossible), so the supremum is 0 and the hypothesis carries no information at all.
* But greedyMatching P pts = (∅, pts) for EVERY list pts: greedyStep only inserts s(u,v) when P (insert s(u,v) M) holds, i.e. when `insert s(u,v) M = ∅`, which is never true since that finset is nonempty. Hence (greedyMatching P pts).1.card = 0 for all pts, and the required conclusion `(greedyMatching P pts).1.card = 1` is unsatisfiable.

So the conclusion `∃ pts, ... ∧ (greedyMatching P pts).1.card = ℓ` fails.

Two root causes of the falsity (both worth fixing in any restatement):
(1) `p ≤ segment_blocking_number P ℓ` says nothing when the defining set of cardinalities is empty (or, more generally, when p = 0): the recorded proof plan implicitly assumed a genuine witness family L with card ℓ satisfying P that blocks p points, which the hypothesis does not supply.
(2) Even with p ≥ 1 and a nonempty witness set the statement fails, because degenerate pairs s(x,x) are legitimate members of a P-satisfying blocking family, while greedy on a duplicate-free list can never insert a pair with equal endpoints: u is taken from the unmatched (hence already seen, distinct) list and v is the new point. Concretely P := fun t => t ⊆ {s(((0:ℝ),(0:ℝ)),((0:ℝ),(0:ℝ)))} is hereditary, L := {s((0,0),(0,0))} has card 1, and it blocks every finite point set S with endpoints ∪ S in general position, so segment_blocking_number P 1 is unbounded; yet (greedyMatching P pts).1.card = 0 for every nodup pts, so no ℓ = 1 witness list exists.

Verified in Lean: the negation `¬ (∀ (P) (hP) (ℓ p), p ≤ segment_blocking_number P ℓ → ∃ pts, pts.Nodup ∧ points_in_general_position ↑pts.toFinset ∧ (greedyMatching P pts).1.card = ℓ ∧ ...)` compiles with no sorry and only the standard axioms.
-/

theorem not_greedy_fraction_le_of_blocking_ge : ¬ (∀ (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (hP : IsHereditarySegmentProperty P) (ℓ p : ℕ)
    (hβ : p ≤ segment_blocking_number P ℓ), ∃ pts : List (ℝ × ℝ), pts.Nodup ∧ points_in_general_position (pts.toFinset : Set (ℝ × ℝ)) ∧
      (greedyMatching P pts).1.card = ℓ ∧
      (2 * (ℓ : ℝ)) / (pts.length : ℝ) ≤ (2 * (ℓ : ℝ)) / (2 * (ℓ : ℝ) + (p : ℝ))) := by
  classical
  intro h
  have hP : IsHereditarySegmentProperty (fun t : Finset (Sym2 (ℝ × ℝ)) => t = ∅) := by
    refine ⟨rfl, ?_⟩
    intro a b hab hb
    rw [hb] at hab
    exact Finset.subset_empty.mp hab
  have step : ∀ (P : Finset (Sym2 (ℝ × ℝ)) → Prop) (M : Finset (Sym2 (ℝ × ℝ)))
      (U : List (ℝ × ℝ)) (v : ℝ × ℝ),
      (∀ x ∈ U, decide (P (insert s(x, v) M)) = false) → greedyStep P (M, U) v = (M, U ++ [v]) := by
    intro P M U v hh
    have hfind : List.find? (fun x => decide (P (insert s(x, v) M))) U = none := by
      rw [List.find?_eq_none]
      intro x hx
      rw [hh x hx]
      simp
    simp only [greedyStep]
    rw [hfind]
  have key : ∀ (pts U : List (ℝ × ℝ)),
      List.foldl (greedyStep (fun t : Finset (Sym2 (ℝ × ℝ)) => t = ∅)) (∅, U) pts
        = (∅, U ++ pts) := by
    intro pts
    induction pts with
    | nil => intro U; simp
    | cons v rest ih =>
      intro U
      rw [List.foldl_cons]
      rw [step (fun t : Finset (Sym2 (ℝ × ℝ)) => t = ∅) ∅ U v (fun x hx => by simp)]
      simpa using ih (U ++ [v])
  have h1 := h (fun t : Finset (Sym2 (ℝ × ℝ)) => t = ∅) hP 1 0 (Nat.zero_le _)
  obtain ⟨pts, hnodup, hgen, hcard, hratio⟩ := h1
  have hkey := key pts []
  simp only [greedyMatching] at hcard
  rw [hkey] at hcard
  simp at hcard
