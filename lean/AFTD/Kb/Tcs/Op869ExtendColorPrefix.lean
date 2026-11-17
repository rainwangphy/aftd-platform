import AFTD.Prelude
import AFTD.Kb.Tcs.Op869ExtendColors

/-!
# op869_extend_color_prefix

Topic: online_algorithms   Node: 5414b5ecabc3

Provenance: helper lemma. Padding and monotonicity for the finite adversary game of arXiv:2610.41516 Section 2.

Before the original vertex bound, padding leaves the set of colors in each prefix unchanged.
-/

/-- Before the original vertex bound, padding leaves the set of colors in each prefix unchanged. -/
theorem op869_extend_color_prefix {n m : ℕ} (h : n ≤ m) (C : Fin n → Finset ℕ) (i : ℕ) (hi : i < n) :
    ((Finset.univ.filter (fun a : Fin m => a.val ≤ i)).biUnion (op869_extend_colors h C)) =
      (Finset.univ.filter (fun a : Fin n => a.val ≤ i)).biUnion C := by
  classical
  ext c
  simp only [Finset.mem_biUnion, Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨a, ha, hc⟩
    have ha' : a.val < n := lt_of_le_of_lt ha hi
    refine ⟨⟨a.val, ha'⟩, ha, ?_⟩
    simpa [op869_extend_colors, ha'] using hc
  · rintro ⟨a, ha, hc⟩
    refine ⟨Fin.castLE h a, ha, ?_⟩
    simpa [op869_extend_colors, a.isLt] using hc
