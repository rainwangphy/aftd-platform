import AFTD.Prelude

/-!
# greedyStep

Topic: online_algorithms   Node: 7a19edd91031

Provenance: formalization of a published result. Source: arXiv:2610.23130, Section 1

Given a predicate P : Finset (Sym2 (ℝ × ℝ)) → Prop, a state (M, U) consisting of a finite set of matched unordered pairs M : Finset (Sym2 (ℝ × ℝ)) and a list of unmatched points U : List (ℝ × ℝ), and an arriving point v : ℝ × ℝ, greedyStep searches U in order for the first point u such that P holds on the insertion of s(u, v) into M; if found, it returns (insert s(u, v) M, U.erase u), and if no such u exists, it returns (M, U ++ [v]).
-/

/-- One step of the greedy matching algorithm upon arrival of a new point v. -/
noncomputable def greedyStep (P : Finset (Sym2 (ℝ × ℝ)) → Prop)
    (state : Finset (Sym2 (ℝ × ℝ)) × List (ℝ × ℝ)) (v : ℝ × ℝ) :
    Finset (Sym2 (ℝ × ℝ)) × List (ℝ × ℝ) := open scoped Classical in
  let (M, U) := state
  match U.find? (fun u => P (insert s(u, v) M)) with
  | some u => (insert s(u, v) M, U.erase u)
  | none => (M, U ++ [v])
