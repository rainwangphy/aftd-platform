import AFTD.Prelude

/-!
# segment_endpoints

Topic: online_algorithms   Node: ec57e56e8199

Provenance: formalization of a published result. Source: arXiv:2610.23130, Definition 1.1

Given a finite set L : Finset (Sym2 (ℝ × ℝ)) of unordered pairs of points in ℝ × ℝ, segment_endpoints L is the finset of type Finset (ℝ × ℝ) of all endpoints of pairs in L, defined by taking the Finset.biUnion over all unordered pairs in L of their two endpoints.
-/

/-- The finset of all endpoints of segments in a finite family L in Sym2 (ℝ × ℝ). -/
noncomputable def segment_endpoints (L : Finset (Sym2 (ℝ × ℝ))) : Finset (ℝ × ℝ) := Finset.biUnion L (fun e => Sym2.lift ⟨fun u v => ({u, v} : Finset (ℝ × ℝ)), by
    intro u v; ext x; simp [Finset.mem_insert, Finset.mem_singleton, or_comm]⟩ e)
