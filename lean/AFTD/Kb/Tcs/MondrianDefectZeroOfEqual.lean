import AFTD.Prelude
import AFTD.Kb.Tcs.MondrianDefect
import AFTD.Kb.Tcs.MondrianRectArea

/-!
# mondrian_defect_zero_of_equal

Topic: combinatorics   Node: 60bd44bd1b6d

Provenance: helper lemma. Helper for OP-280 and mondrian_perfect_partition_large_prime_iff. Related work: arXiv:2610.19193, Section 1 (perfect partitions and scaling); arXiv:2007.09639, Theorem 4.1 (available shapes and prime-power exclusions).

A rectangle list whose members all have the same area has defect zero, including the empty list.
-/

theorem mondrian_defect_zero_of_equal (P : List (ℕ × ℕ × ℕ × ℕ)) (A : ℕ)
    (h : ∀ r ∈ P, mondrian_rect_area r = A) : mondrian_defect P = 0 := by
  have he : P.map mondrian_rect_area = List.replicate P.length A := by
    apply List.eq_replicate_iff.mpr
    refine ⟨by simp, ?_⟩
    intro b hb
    obtain ⟨r, hr, rfl⟩ := List.mem_map.mp hb
    exact h r hr
  simp [mondrian_defect, he, List.max?_replicate, List.min?_replicate]
